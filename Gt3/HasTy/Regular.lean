import Gt3.HasTy.Basic
import Gt3.JEq.Regular

theorem Ctx.HasTy.regular {Γ A a} (h : HasTy Γ A a) : IsTy Γ A := h.refl.regular
