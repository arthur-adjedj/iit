import IIT

mutual

iit Con : Type where
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit Tm : (Γ : Con) → (A : Ty Γ) → Type where
| El : (Δ : Con) → Tm Δ (Ty.U Δ)

iit_termination
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ (Γ.ih _).2 _).1)
  repeat assumption
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ (Γ.ih _).2 _).2)
  apply Ty.pi.m (A.m := (A.ih _ _ _ _).1) (B.m := (B.ih _ _ _ _).1)
  repeat assumption
  apply Con.ext.r (A.r := (A.ih _ _ _ _).2)
  repeat assumption
  apply Ty.pi.r (A.r := (A.ih _ _ _ _).2) (B.r := (B.ih _ _ _ _).2)
  repeat assumption
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ (Γ.ih _).2 _).1)
  repeat assumption
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ (Γ.ih _).2 _).2)
  apply Ty.pi.m (A.m := (A.ih _ _ _ _).1) (B.m := (B.ih _ _ _ _).1)
  repeat assumption
  apply Con.ext.r (Γ.m := Γ.m) (A.r := (A.ih _ _ _ _).2)
  repeat assumption
  apply Ty.pi.r (A.r := (A.ih _ _ _ _).2) (B.r := (B.ih _ _ _ _).2)
  repeat assumption
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ _ _).1)
  repeat assumption
  apply (Γ.ih _).2
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
  apply Ty.pi.m (A.m := (A.ih _ _ _ _).1) (B.m := (B.ih _ _ _ _).1)
  repeat assumption
  apply Con.ext.r (Γ.m := Γ.m) (A.r := (A.ih _ _ _ _).2)
  repeat assumption
  apply Ty.pi.r (A.r := (A.ih _ _ _ _).2) (B.r := (B.ih _ _ _ _).2)
  repeat assumption


end
