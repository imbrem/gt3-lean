import Gt3.HasTy.Factor
import Gt3.JEq.Regular
import Gt3.SubTy.Basic

theorem Ctx.HasTy.regular {Γ A a} (h : HasTy Γ A a) : IsTy Γ A := h.refl.regular

theorem Ctx.InnerTy.regular {Γ A a} (h : InnerTy Γ A a) : IsTy Γ A := h.toTy.regular

theorem Ctx.OuterTy.regular {Γ A a} (h : OuterTy Γ A a) : IsTy Γ A := h.toTy.regular

theorem Ctx.OuterTy.factor {Γ A a} (h : OuterTy Γ A a) : ∃W, InnerTy Γ W a ∧ SubTy Γ W A
  := by induction h with
  | base h => exact ⟨_, h, .refl h.regular⟩
  | cast_level h I => have ⟨W, ha, hw⟩ := I; exact ⟨W, ha, hw.cast_level⟩
  | cast he _ I => have ⟨W, ha, hw⟩ := I; exact ⟨W, ha, hw.cast he⟩

theorem Ctx.HasTy.factor₂ {Γ A a} (h : HasTy Γ A a) : ∃W, InnerTy Γ W a ∧ SubTy Γ W A
  := h.factor.factor
