import Gt3.JEq.Basic
import Gt3.Universe.Syntax

def Ctx.JEq.us {Γ A a b} (h : Ctx.JEq Γ A a b) (σ : ULevel.Subst)
  : Ctx.JEq (Γ.us σ) (A.us σ) (a.us σ) (b.us σ) := by
  induction h with
  | fv' _ hΓ =>
    simp
    constructor
    · assumption
    · exact hΓ.us
  | cons_ok =>
    apply cons_ok
    · assumption
    · simp [*]
    · assumption
  | cast_level_le h _ IA =>
    simp at *
    apply cast_level_le _ IA
    apply ULevel.subst_mono; assumption
  | cast' => apply cast' <;> assumption
  | symm => apply symm; assumption
  | trans => apply trans <;> assumption
  | transfer' => apply transfer' <;> assumption
  | eqn_rfl => apply eqn_rfl <;> assumption
  | prop_inhab_unit' => apply prop_inhab_unit' <;> assumption
  | choose_spec' _ _ _ _ _ _ _ IA IAI Iφ IAφI Iφc Ilhs Irhs =>
    simp at *
    constructor
    · exact IA
    · exact IAI
    · assumption
    · assumption
    · assumption
    · assumption
    · assumption
  | _ => simp at *; constructor <;> assumption

-- TODO: IsWf, IsTy, and friends
