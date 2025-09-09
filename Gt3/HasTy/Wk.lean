import Gt3.HasTy.Basic
import Gt3.JEq.Wk

theorem Ctx.HasTy.psub {Γ Δ} (h : PSub Γ Δ) {A a : Tm 0} (hab : HasTy Δ A a)
  : HasTy Γ A a := by induction hab generalizing Γ with
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
