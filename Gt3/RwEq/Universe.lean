import Gt3.RwEq.Erase
import Gt3.JEq.Universe

namespace Gt3

theorem Ctx.KWEq.us (σ : ULevel.Subst) {Γ a b} (h : Ctx.KWEq Γ a b)
  : Ctx.KWEq (Γ.us σ) (a.us σ) (b.us σ) := by convert WfEq.us σ h; simp [KWEq]

theorem Ctx.KEq.us (σ : ULevel.Subst) {Γ a b} (h : Ctx.KEq Γ a b)
  : Ctx.KEq (Γ.us σ) (a.us σ) (b.us σ)
  := by induction h with
  | wf_clamp h => exact KEq.wf_clamp (h.us σ)
  | trans => apply trans <;> assumption
  | _ => constructor <;> assumption

end Gt3
