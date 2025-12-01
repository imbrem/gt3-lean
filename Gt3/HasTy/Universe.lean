import Gt3.HasTy.Regular
import Gt3.JEq.Universe

namespace Gt3

theorem Ctx.HasTy.us (σ : ULevel.Subst) {Γ A a} (h : Ctx.HasTy Γ A a)
  : Ctx.HasTy (Γ.us σ) (A.us σ) (a.us σ)
  := (h.refl.us σ).lhs_ty

end Gt3
