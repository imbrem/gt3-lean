import Gt3.JEq.Basic
import Gt3.Universe.Syntax

theorem Ctx.JEq.us (σ : ULevel.Subst) {Γ A a b} (h : Ctx.JEq Γ A a b)
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

theorem Ctx.TyEq.us (σ : ULevel.Subst) {Γ A B} (h : Ctx.TyEq Γ A B)
  : Ctx.TyEq (Γ.us σ) (A.us σ) (B.us σ) := have ⟨ℓ, h⟩ := h; ⟨ℓ.subst σ, h.us σ⟩

theorem Ctx.WfEq.us (σ : ULevel.Subst) {Γ a b} (h : Ctx.WfEq Γ a b)
  : Ctx.WfEq (Γ.us σ) (a.us σ) (b.us σ) := have ⟨A, h⟩ := h; ⟨A.us σ, h.us σ⟩

theorem Ctx.IsWf.us (σ : ULevel.Subst) {Γ a} (h : Ctx.IsWf Γ a)
  : Ctx.IsWf (Γ.us σ) (a.us σ) := WfEq.us σ h

theorem Ctx.IsTy.us (σ : ULevel.Subst) {Γ A} (h : Ctx.IsTy Γ A)
  : Ctx.IsTy (Γ.us σ) (A.us σ) := TyEq.us σ h

theorem Ctx.IsUniv.us (σ : ULevel.Subst) {Γ A} (h : Ctx.IsUniv Γ A)
  : Ctx.IsUniv (Γ.us σ) (A.us σ) := have ⟨ℓ, h⟩ := h; ⟨ℓ.subst σ, h.us σ⟩

theorem Ctx.IsInhab.us (σ : ULevel.Subst) {Γ A} (h : Ctx.IsInhab Γ A)
  : Ctx.IsInhab (Γ.us σ) (A.us σ) := TyEq.us σ h
