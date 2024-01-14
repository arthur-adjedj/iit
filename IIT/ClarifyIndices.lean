import Lean
import IIT.Util

open Lean
open Elab
open Meta

namespace Lean

namespace Meta

section

open AssocList

def fVarSubstBackwardGet? (s : AssocList FVarId Expr) (e : Expr) : Option FVarId :=
match s with
| nil => none
| cons k v tl => if v == e then some k
                 else fVarSubstBackwardGet? tl e

end

def containsUnknownFVars? (mVar : MVarId) (e : Expr) : MetaM Bool :=
match e with
| Expr.fvar v => Lean.MVarId.withContext mVar do
  match ← Lean.FVarId.findDecl? v with
  | some _ => return false
  | none   => return true
| Expr.app f e => containsUnknownFVars? mVar f <||> containsUnknownFVars? mVar e
| Expr.lam _ t b _ => containsUnknownFVars? mVar t <||> containsUnknownFVars? mVar b
| Expr.forallE _ t b _ => containsUnknownFVars? mVar t <||> containsUnknownFVars? mVar b
| Expr.letE _ e t b _ => containsUnknownFVars? mVar e <||> containsUnknownFVars? mVar t
                                                      <||> containsUnknownFVars? mVar b
| Expr.mdata _ e => containsUnknownFVars? mVar e
| Expr.proj _ _ e => containsUnknownFVars? mVar e
| _ => return false

def substituteWithCasesOn (mVar : MVarId) (fVar : FVarId) (e : Expr) : MetaM Expr :=
Lean.MVarId.withContext mVar do
  let eqSubgoals ← Lean.MVarId.cases (← mkFreshExprMVar $ mkConst `True).mvarId! fVar
  Lean.MVarId.withContext mVar do
    unless eqSubgoals.size > 0 do
      return e
    let substResult := eqSubgoals[0]!.subst.apply e
    -- In case of a trivial substitution, look for a expression that is mapped _to_ e and return that one
    if ← isDefEq substResult e then
      match fVarSubstBackwardGet? eqSubgoals[0]!.subst.map e with
      | some fVar' => return eqSubgoals[0]!.subst.apply $ mkFVar fVar'
      | none       => return substResult
    return substResult

def clarifyIndexFalse (mVar : MVarId) (fVar : FVarId) : MetaM Unit :=
Lean.MVarId.withContext mVar do
  let falseMVar ← mkFreshExprMVar $ mkConst `False
  let eqSubgoals ← Lean.MVarId.cases falseMVar.mvarId! fVar
  unless eqSubgoals.size == 0 do throwTacticEx `clarifyIndices mVar "something wrong here"
  let ff ← instantiateMVars falseMVar
  let fMVar ← mkFreshExprMVar $ mkForall "eq" BinderInfo.default (mkConst `False) (← mVar.getType)
  Lean.MVarId.assign mVar $ mkApp fMVar ff
  let (ffFVar, bodyMVar) ← Lean.MVarId.intro fMVar.mvarId! "eq"
  Lean.MVarId.withContext bodyMVar do
    let _ ← Lean.MVarId.cases bodyMVar ffFVar
    return

def clarifyIndex (mVar : MVarId) (fVar : FVarId) (i : Nat := 0) : MetaM (Option $ FVarSubst × MVarId) :=
  Lean.MVarId.withContext mVar do
    let type ← inferType $ mkFVar fVar
    let target ← Lean.MVarId.getType mVar
    let failEx := fun _ => throwTacticEx `clarifyIndices mVar "inductive type expected"
    type.withApp fun f args => matchConstInduct f failEx fun val _ => do
      unless val.numParams + i < args.size do throwTacticEx `clarifyIndices mVar "not enough indices"
      let rhs := args.get! (val.numParams + i)
      unless rhs.isFVar do return (FVarSubst.empty, mVar) --consider failing instead
      let lhs ← mkFreshExprMVar $ ← inferType rhs
      -- First cases run to determine the lhs of the equation
      let substResult ← try substituteWithCasesOn mVar fVar rhs
                        catch _ => throwTacticEx `clarifyIndices mVar "unknown free variables in substitution result"
      -- TODO: Instead of rejecting here, we should, instead of an equality, prove an existential containing the new free vars
      if ← containsUnknownFVars? mVar substResult then
        throwTacticEx `clarifyIndices mVar "unknown free variables in substitution result"
      Lean.MVarId.assign lhs.mvarId! substResult
      -- Second cases run to actually prove the equality
      let eqType ← mkEq lhs rhs
      let eqMVar ← mkFreshExprMVar eqType
      let eqSubgoals ← Lean.MVarId.cases eqMVar.mvarId! fVar
      if eqSubgoals.size == 0 then
        clarifyIndexFalse mVar fVar
        return none
      unless eqSubgoals.size == 1 do
        throwTacticEx `clarifyIndices eqMVar.mvarId! "indices must determine constructor uniquely"
      let u ← getLevel (← inferType lhs)
      eqSubgoals[0]!.mvarId.assign  $ mkApp2 (mkConst `rfl [u]) (← inferType lhs) lhs
      -- Intro the equality as an fVar
      let fMVar ← mkFreshExprMVar $ mkForall "eq" BinderInfo.default eqType target
      Lean.MVarId.assign mVar $ mkApp fMVar eqMVar
      let (eqFVar, bodyMVar) ← Lean.MVarId.intro fMVar.mvarId! "eq"
      Lean.MVarId.withContext bodyMVar do
        -- Apply cases on the equality
        let eqCases ← Lean.MVarId.cases bodyMVar eqFVar
        unless eqCases.size == 1 do throwTacticEx `clarifyIndices bodyMVar "could not apply cases on resulting equality"
        let mut mVar' := eqCases[0]!.mvarId
        Lean.MVarId.withContext mVar' do
          let eqFVar := eqCases[0]!.subst.apply $ mkFVar eqFVar
          let mut mVar' := mVar'
          if let Expr.fvar id .. := eqFVar then
            try mVar' ← Lean.MVarId.clear mVar' id catch _ => pure ()
          return (eqCases[0]!.subst, mVar')

def clarifyIndicesTac (mVar : MVarId) (fVar : FVarId) : MetaM (Option $ FVarSubst × MVarId) :=
  Lean.MVarId.withContext mVar do
    mVar.checkNotAssigned `clarifyInstances
    let type ← inferType $ mkFVar fVar
    let failEx := fun _ => throwTacticEx `clarifyIndices mVar "inductive type expected"
    type.withApp fun f args => matchConstInduct f failEx fun val _ => do
      unless val.numIndices > 0 do throwTacticEx `clarifyIndices mVar "indexed inductive type expected"
      unless args.size == val.numIndices + val.numParams do throwTacticEx `clarifyIndices mVar "ill-formed inductive datatype"
      let mut mVar := mVar
      let mut subst := FVarSubst.empty
      for i in [:val.numIndices] do
        let fVar := subst.apply $ mkFVar fVar
        match ← clarifyIndex mVar fVar.fvarId! i with
        | some  (s, mVar') => mVar := mVar'
                              subst := subst.append s
        | none             => return none
      return (subst, mVar)

end Meta

open Tactic

syntax (name := clarifyIndices) "clarifyIndices" (colGt ident)+ : tactic
@[tactic clarifyIndices] def elabClarifyIndices : Tactic
| `(tactic|clarifyIndices $fVars*) => do
  forEachVar fVars fun mVar fVar => do
  match ← Meta.clarifyIndicesTac mVar fVar with
  | some (_, mVar) => return mVar
  | none           => return mVar
| _ => throwUnsupportedSyntax

end Lean

-- Examples
/-namespace ClarifyIndicesExamples

inductive Foo : (n : Nat) → Fin n → Prop
| mk1 : Foo 5 0
| mk2 : Foo 8 3

def bar (x : Fin 5) (p : Foo 5 x) (A : Type) (a : Foo 5 0 → A) : A := by
  clarifyIndices p
  exact a p

def baz (p : Foo 9 x) (A : Type) : A := by
  clarifyIndices p

inductive Foo' : (m n : Nat) → Fin (m + n) → Prop
| mk1 : Foo' 4 2 0
| mk2 : Foo' 1 3 1

def bar' (y : Nat) (x : Fin 6) (p : Foo' 4 2 x) (A : Type) (a : Foo' 4 2 0 → A) : A := by
  clarifyIndices p
  exact a p

inductive Foo'' : (m n l : Nat) → Prop
| mk1 : Foo'' 1 2 3
| mk2 : (x : Nat) → Foo'' 4 x 6

def bar'' (x y : Nat) (p : Foo'' x y 3) (h : x < y) : Foo'' x 2 3 := by
  clarifyIndices p
  exact p

def bar''' (x y : Nat) (p : Foo'' 4 (x + 1) y) : Foo'' 4 (x + 1) 6 := by
  clarifyIndices p
  exact p

inductive Foo''' : (m n : Nat) → (b : Bool) → Prop
| mk1 : (n : Nat) → Foo''' n n true
| mk2 : Foo''' 0 1 false

def bar4 (m n : Nat) (p : Foo''' m n true) : Foo''' m m true := by
  clarifyIndices p
  exact p

inductive Fooo : (n l : Nat) → Prop
| mk1 : (x y : Nat) → Fooo (x + y) 0
| mk2 : Fooo 8 3

def baar (x : Nat) (p : Fooo x 0) (A : Type) (a : Fooo (2 + 3) 0 → A) : A := by
  clarifyIndices p
  skip


end ClarifyIndicesExamples-/
