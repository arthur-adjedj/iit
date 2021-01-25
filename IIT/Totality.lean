/- Proves the totality of the eliminator relation -/

import IIT.Relation
import Lean.Elab.Tactic

open Lean
open Elab
open Command
open Meta
open Expr
open Array
open Tactic

namespace IIT

variables (its : List InductiveType) (ls : List Level)
  (motives : Array Expr) (methods : Array (Array Expr))

partial def totalityType (l : Level) (e sref dref rref : Expr) : MetaM Expr := do
match e with
| forallE n t b _ => 
  match headerAppIdx? its t with
  | some _ => let t' := liftBVarsOne t
              let tm := mkApp (motiveAux its motives t' t) $ mkBVar 0
              let tr ← elimRelationCtorTmS its motives methods (liftBVarsTwo t) t'
              let tr := mkApp (mkApp tr $ mkBVar 1) $ mkBVar 0
              let sref := mkApp (liftBVarsThree sref) $ mkBVar 2
              let dref := mkApp (mkApp (liftBVarsThree dref) $ mkBVar 2) $ mkBVar 1
              let rref := mkApp (mkApp (liftBVarsThree rref) $ mkBVar 2) $ mkBVar 1
              mkForall n e.binderInfo t $
              mkForall (n ++ motiveSuffix) BinderInfo.implicit tm $
              mkForall (n ++ relationSuffix) BinderInfo.default tr $
              ← totalityType l (liftBVarsTwo b) sref dref rref
  | none   => let sref := mkApp (liftBVarsOne sref) $ mkBVar 0
              let dref := mkApp (liftBVarsOne dref) $ mkBVar 0
              let rref := mkApp (liftBVarsOne rref) $ mkBVar 0
              mkForall n e.binderInfo t $
              ← totalityType l b sref dref rref
| sort l _  => let dref := liftBVarsOne dref
               let rref := liftBVarsOne rref
               mkForall "s" BinderInfo.default sref $
               mkSigma l (mkApp dref $ mkBVar 0) (mkApp rref $ mkBVar 0)
| _ => e

partial def totalityTypes (i : Nat := 0) (decls : List Declaration := []) : MetaM $ List Declaration :=
if i >= its.length then decls else do
let name := (its.get! i).name
let type := (its.get! i).type
let rref := mkAppN (mkConst $ name ++ relationSuffix) (motives ++ methods.concat)
let tot ← totalityType its motives methods (ls.get! i) type (mkConst name) motives[i] rref --TODO level
let tot ← mkForallFVars (motives ++ methods.concat) tot
let type ← inferType tot
let decl := Declaration.defnDecl { name     := name ++ "tot",
                                   lparams  := [], -- TODO
                                   value    := tot,
                                   type     := type,
                                   hints    := arbitrary -- TODO
                                   safety   := DefinitionSafety.safe }
totalityTypes (i + 1) (decls.append [decl])

open Lean.Parser
open Lean.Elab.Command
open Lean.Elab.Term

private partial def introMethods (mVar : MVarId) (ctorIdss : List (List Name)) (i : Nat := 0) (fVarss : Array (Array FVarId) := #[]) :
  MetaM (Array (Array FVarId) × MVarId) :=
if i >= ctorIdss.length then return (fVarss, mVar) else do
let (fVars, mVar) ← introN mVar (ctorIdss.get! i).length ((ctorIdss.get! i).map fun n => n ++ "m")
introMethods mVar ctorIdss (i + 1) (fVarss.push fVars)

inductive HeaderArg where
| internal : FVarId → FVarId → FVarId → HeaderArg
| external : FVarId → HeaderArg

private def HeaderArg.toExpandedExprs (ha : HeaderArg) : Array Expr :=
match ha with
| internal s m r => #[mkFVar s, mkFVar m, mkFVar r]
| external n     => #[mkFVar n]

private partial def introHdArgs (mVar : MVarId) (hdType : Expr) (has : Array HeaderArg := #[]) :
  MetaM (Array HeaderArg × MVarId) := do --TODO swap FVarId for annotated child type
match hdType with
| forallE n t b _ =>
  match headerAppIdx? its t with
  | some _ => let (fVars', mVar) ← introN mVar 3 [n, n ++ motiveSuffix, n ++ relationSuffix]
              let ha := HeaderArg.internal fVars'[0] fVars'[1] fVars'[2]
              introHdArgs mVar b (has.push ha)
  | none   => let (fVar, mVar) ← intro mVar n
              introHdArgs mVar b (has.push $ HeaderArg.external fVar)
| _ => return (has, mVar)

private partial def totalityRecMotiveAux_old (e : Expr) 
  (wref rref : Expr) (mainE : Expr) : MetaM Expr := do
match e with
| forallE n t b _ => 
  match headerAppIdx? its t with
  | some j => mkForallM n e.binderInfo t fun sFVar => do
                let se := mkFst sFVar
                let sw := mkSnd sFVar
                let m := mkApp (← methodTmS its methods motives t t) sFVar
                mkForallM (n ++ motiveSuffix) BinderInfo.default m fun mFVar => do
                  let r := mkAppN (← elimRelationCtorTmS its motives methods t t) #[sFVar, mFVar]
                  mkForallM (n ++ relationSuffix) BinderInfo.default r fun rFVar => do
                    let wref := mkApp wref se
                    let rref := mkAppN rref #[sFVar, mFVar]
                    totalityRecMotiveAux_old b wref rref mainE
  | none   => mkForallM n e.binderInfo t fun extFVar => do
                let wref := mkApp wref extFVar
                let rref := mkApp rref extFVar
                totalityRecMotiveAux_old b wref rref mainE
| sort l _        => let w := mkApp wref mainE
                     mkForallM "mainw" BinderInfo.default w fun mainw => do
                       mkSigmaM $ mkApp rref $ ← mkPair mainE mainw
| _ => e

private partial def totalityRecMotiveAux (e : Expr) 
  (wref rref : Expr) (mainE : Expr) (em er : Expr := e) : MetaM Expr := do
match e with
| forallE n t b _ => do
  match headerAppIdx? its t with
  | some j => (let m := mkApp (← methodTmS its methods motives (liftBVarsOne t) (liftBVarsOne $ bindingDomain! em)) (mkBVar 0)
               let r := mkAppN (← elimRelationCtorTmS its motives methods (liftBVarsTwo t) (liftBVarsTwo $ bindingDomain! er))
                          #[mkBVar 1, mkBVar 0]
	       let wref := mkApp (liftBVarsThree wref) $ mkFst $ mkBVar 2
	       let rref := mkAppN (liftBVarsThree rref) #[mkBVar 2, mkBVar 1]
	       let b'   := liftBVarsTwo b
	       let bm   := liftBVarsOne $ bindingBody! em
	       let br   := bindingBody! er
               return mkForall n e.binderInfo t $
                 mkForall (n ++ motiveSuffix) BinderInfo.default m $
	         mkForall (n ++ relationSuffix) BinderInfo.default r $
	         ← totalityRecMotiveAux b' wref rref mainE bm br)
  | none => let wref := mkApp (liftBVarsOne wref) (mkBVar 0)
            let rref := mkApp (liftBVarsOne wref) (mkBVar 0)
            let bm   := bindingBody! em
            let br   := bindingBody! er
            mkForall n e.binderInfo t $
             ← totalityRecMotiveAux b wref rref mainE bm br
| _ => let w := mkApp wref mainE
       mkForallM "mainw" BinderInfo.default w fun mainw => do
         mkSigmaM $ liftBVarsTwo $ mkApp rref $ ← mkPair mainE mainw --????

private def totalityRecMotive (hIdx : Nat) (its : List InductiveType) : MetaM Expr :=
let name := (its.get! hIdx).name
let type := (its.get! hIdx).type
let rref := mkAppN (mkConst (name ++ relationSuffix)) (motives ++ methods.concat)
mkLambdaM "mainE" BinderInfo.default (mkConst $ name ++ erasureSuffix) fun EFVar =>
  totalityRecMotiveAux its motives methods (its.get! hIdx).type (mkConst $ name ++ wellfSuffix) rref EFVar

def sMainName : Name := "S"

instance : Inhabited CasesSubgoal := Inhabited.mk $ CasesSubgoal.mk arbitrary ""

def totalityOuterTac (hIdx : Nat) (its : List InductiveType) : TacticM Unit := do
  let mainIT := its.get! hIdx
  let (mVar, _) ← getMainGoal
  let hType ← inferType $ mkConst mainIT.name --TODO levels?
  let (motives, mVar) ← introN mVar its.length (its.map fun it => it.name ++ "m")
  let (methodss, mVar) ← introMethods mVar (its.map fun it => it.ctors.map fun ctor => ctor.name)
  let methods := methodss.concat
  let (hArgs,   mVar) ← introHdArgs its mVar hType
  let (sMain,   mVar) ← intro mVar sMainName
  let (sCasesSubgoals) ← cases mVar sMain #[[sMainName ++ erasureSuffix, sMainName ++ wellfSuffix]]
  let mVar := sCasesSubgoals[0].mvarId
  let mainE := sCasesSubgoals[0].fields[0]
  let mainw := sCasesSubgoals[0].fields[1]
  let motives  := motives.map mkFVar
  let methodss := methodss.map fun ms => ms.map mkFVar
  let methods  := methods.map mkFVar
  withMVarContext mVar do
    let mut recMotives := #[]
    for i in [:its.length] do
      let mot ← totalityRecMotive motives methodss i its
      recMotives := recMotives.push mot
    let recApp := mkAppN (mkConst (mainIT.name ++ erasureSuffix ++ "rec") [levelOne]) recMotives --TODO levels
    --throwTacticEx "totalityOuter" mVar recApp
    let (methodGoals, recApp) ← appExprHoleN methods.size recApp --TODO
    let recApp := mkApp recApp mainE
    let recApp := mkAppN recApp $ (hArgs.map HeaderArg.toExpandedExprs).concat
    let recApp := mkApp recApp mainw
    assignExprMVar mVar recApp
    --throwTacticEx "totalityOuter" mVar $ sCasesSubgoals[0].subst.get sMain
    setGoals $ (← getGoals) ++ methodGoals

#check InductionSubgoal.fields
    
instance : Inhabited (Syntax.SepArray ",") := Inhabited.mk $ Syntax.SepArray.ofElems #[]

syntax idList := "[" ident,+,? "]"
syntax (name := totalityOuter) "totalityOuter" num idList+ : tactic
@[tactic totalityOuter] def elabTotalityOuter : Tactic
  | `(tactic|totalityOuter $i $[[$idss,*]]*) => do
    let i := Syntax.toNat i
    let hIds := idss[0].getElems.map Syntax.getId
    let ctorIdss := idss[1:]
    let ctorIdss := ctorIdss.toArray.map fun ctors => ctors.getElems.map Syntax.getId
    let hTypes := hIds.mapM fun hId => inferType $ mkConst hId
    let (its : List InductiveType) ← (List.zip hIds.toList ctorIdss.toList).mapM fun (hId, ctorIds) => do
      let hType ← inferType $ mkConst hId
      let ctors ← ctorIds.mapM λ ctorId => do
        let ctorType ← inferType $ mkConst ctorId
        return { name := ctorId, type := ctorType }
      return { name := hId, type := hType, ctors := ctors.toList : InductiveType } --TODO
    totalityOuterTac i its
  | _  => throwUnsupportedSyntax


end IIT
