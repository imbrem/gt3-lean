import Gt3.HasTy.Basic
import Gt3.JEq.Wk

theorem Ctx.HasTy.psub {Γ Δ} (h : PSub Γ Δ) {A a : Tm 0} (hab : HasTy Δ A a)
  : HasTy Γ A a := by induction hab generalizing Γ with
  | transfer hA hB IA => exact (IA h).transfer (hB.psub h)
  | _ =>
    constructor <;> first
    | apply_assumption <;> assumption
    | {
      rename Finset String => L
      intro x hx
      have ⟨hL, hΓ⟩ : x ∉ L ∧ x ∉ Γ.dv := by rw [<-Finset.notMem_union]; exact hx
      apply_assumption
      · exact hL
      · apply PSub.cons'
        <;> first | assumption | apply HasTy.is_ty <;> apply_assumption <;> assumption
    }
    | exact h.left_ok
    | apply Ctx.TyEq.psub <;> assumption
    | apply h.is_perm; assumption

theorem Ctx.HasTy.wk0 {Γ A a} (ha : HasTy Γ A a) {x B} (hx : x ∉ Γ.dv) (hB : Γ.IsTy B)
  : HasTy (Γ.cons x B) A a
  := ha.psub (ha.ok.psub.skip hx hB)

theorem Ctx.TyEq.top_var {Γ : Ctx} {x A B} (hx : x ∉ Γ.dv) (hAB : TyEq Γ A B)
  : HasTy (Γ.cons x A) B (.fv x)
  := .cast (hAB.wk0 hx hAB.lhs) (.fv (hAB.ok.cons hx hAB.lhs) (.here _ _ _))
