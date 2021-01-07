import IIT

--set_option trace.Elab true
--set_option syntaxMaxDepth 10
set_option pp.all true

mutual

iit Con : Type where
| nil : Con
| foo : (b : Bool) → (n : Nat) → Con
| bla : (Γ Δ : Con) → Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U' : Ty Con.nil
| U : (Γ Δ : Con) → Ty Δ
| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit Tm : (Γ : Con) → (A : Ty Γ) → Type where
| El : Tm Con.nil Ty.U'

iit Subb : (Δ Γ : Con) → Type where
| swap : (Δ Γ : Con) → (A : Subb Γ Δ) → Subb Δ Γ

iit Foo : (m n : Nat) → Type where
| bar : Foo 5 3
| baz : (m n : Nat) → (p : Foo n m) → Foo m n

end

example (Γ : Con.E) (W : Ty.w Γ Ty.U'.E) : Γ = Con.nil.E := by _
