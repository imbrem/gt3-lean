import Gt3.JEq.Basic

inductive Ctx.SubTy : Ctx → Tm 0 → Tm 0 → Prop
  | refl {Γ A} (hA : IsTy Γ A) : SubTy Γ A A
  | cast_level {Γ S ℓ} (hS : SubTy Γ S (.univ ℓ)) : SubTy Γ S (.univ (ℓ + 1))
  | cast {Γ S A A'} (hS : SubTy Γ S A) (hA : TyEq Γ A A') : SubTy Γ S A'

theorem Ctx.SubTy.trans {Γ A B C} (hAB : SubTy Γ A B) (hBC : SubTy Γ B C) : SubTy Γ A C
  := by induction hBC with
  | refl => assumption
  | _ => constructor <;> assumption

theorem Ctx.SubTy.lhs {Γ A B} (h : SubTy Γ A B) : IsTy Γ A := by induction h <;> assumption

theorem Ctx.SubTy.ok {Γ A B} (h : SubTy Γ A B) : Ok Γ := h.lhs.ok

theorem Ctx.SubTy.rhs {Γ A B} (h : SubTy Γ A B) : IsTy Γ B := by cases h with
  | refl h => exact h
  | cast_level h => exact .univ h.ok
  | cast _ h => exact h.rhs

theorem Ctx.SubTy.of_eq {Γ A B} (h : TyEq Γ A B) : SubTy Γ A B := (SubTy.refl h.lhs).cast h

theorem Ctx.SubTy.univ_mpr {Γ A U} (h : SubTy Γ A U) (hU : IsUniv Γ U) : IsUniv Γ A
  := by induction h with
  | refl => assumption
  | cast_level h I => exact I (.univ h.ok)
  | cast h he I => exact I (hU.cast he)

theorem Ctx.SubTy.univ_rhs {Γ A ℓ} (h : SubTy Γ A (.univ ℓ)) : IsUniv Γ A
  := univ_mpr h (.univ h.ok)

theorem Ctx.SubTy.univ_mp {Γ U B} (h : SubTy Γ U B) (hU : IsUniv Γ U) : IsUniv Γ B
  := by induction h with
  | refl => assumption
  | cast_level h => exact .univ h.ok
  | cast h he I => exact I.cast he.symm

theorem Ctx.SubTy.univ_lhs {Γ ℓ B} (h : SubTy Γ (.univ ℓ) B) : IsUniv Γ B
  := univ_mp h (.univ h.ok)

theorem Ctx.SubTy.univ_iff {Γ A B} (h : SubTy Γ A B) : IsUniv Γ A ↔ IsUniv Γ B
  := ⟨h.univ_mp, h.univ_mpr⟩

theorem Ctx.SubTy.univLE {Γ lo hi} (hΓ : Ok Γ) (h : lo ≤ hi) : SubTy Γ (.univ lo) (.univ hi) := by
  induction h with
  | refl => exact .refl (.univ hΓ)
  | step _ I => exact I.cast_level

theorem Ctx.SubTy.not_univ {Γ A B} (h : SubTy Γ A B) (hB : ¬IsUniv Γ B) : TyEq Γ A B := by
  induction h with
  | refl h => exact h
  | cast_level h => exact (hB (.univ h.ok)).elim
  | cast _ h I =>
    apply TyEq.trans (I _) h
    rw [IsUniv.eq_iff h]
    exact hB

theorem Ctx.SubTy.univ_or {Γ A B} (h : SubTy Γ A B) : TyEq Γ A B  ∨ IsUniv Γ B  := by
  convert h.not_univ
  rw [or_iff_not_imp_right]

def Ctx.CmpTy (Γ : Ctx) (A B : Tm 0) := TyEq Γ A B ∨ (IsUniv Γ A ∧ IsUniv Γ B)

theorem Ctx.CmpTy.of_eq {Γ A B} (hAB : TyEq Γ A B) : CmpTy Γ A B := .inl hAB

theorem Ctx.CmpTy.refl {Γ A} (hA : IsTy Γ A) : CmpTy Γ A A := .of_eq hA

theorem Ctx.CmpTy.of_sub {Γ A B} (hAB : SubTy Γ A B) : CmpTy Γ A B := by
  cases hAB.univ_or <;> simp [hAB.univ_iff, CmpTy, *]

theorem Ctx.CmpTy.symm {Γ A B} (hAB : CmpTy Γ A B) : CmpTy Γ B A
  := by cases hAB with | inl h => exact .inl h.symm | inr h => simp [CmpTy, *]

theorem Ctx.CmpTy.lhs_is_ty {Γ A B} (hAB : CmpTy Γ A B) : IsTy Γ A := match hAB with
  | .inl h => h.lhs
  | .inr h => h.left.is_ty

theorem Ctx.CmpTy.rhs_is_ty {Γ A B} (hAB : CmpTy Γ A B) : IsTy Γ B := hAB.symm.lhs_is_ty

@[simp]
theorem Ctx.CmpTy.refl_iff {Γ A} : CmpTy Γ A A ↔ IsTy Γ A := ⟨lhs_is_ty, .refl⟩

theorem Ctx.CmpTy.symm_iff {Γ A B} : CmpTy Γ A B ↔ CmpTy Γ B A := ⟨.symm, .symm⟩

theorem Ctx.CmpTy.left_univ {Γ ℓ B} (h : CmpTy Γ (.univ ℓ) B) : IsUniv Γ B := match h with
  | .inl h => ⟨_, h.symm⟩
  | .inr h => h.right

theorem Ctx.CmpTy.right_univ {Γ A ℓ} (h : CmpTy Γ A (.univ ℓ)) : IsUniv Γ A := h.symm.left_univ

@[simp]
theorem Ctx.CmpTy.left_univ_iff {Γ ℓ B} : CmpTy Γ (.univ ℓ) B ↔ IsUniv Γ B
  := ⟨left_univ, fun h => by simp [CmpTy, h.ok, h]⟩

@[simp]
theorem Ctx.CmpTy.right_univ_iff {Γ A ℓ} : CmpTy Γ A (.univ ℓ) ↔ IsUniv Γ A
  := by rw [symm_iff, left_univ_iff]

theorem Ctx.CmpTy.trans {Γ A B C} (hAB : CmpTy Γ A B) (hBC : CmpTy Γ B C) : CmpTy Γ A C := by
  cases hAB with
  | inl h => cases hBC with
    | inl h' => exact .inl (h.trans h')
    | inr h' => simp [CmpTy, IsUniv.eq_iff h, *]
  | inr h => cases hBC with
  | inl h' => simp [CmpTy, <-IsUniv.eq_iff ‹_›, *]
  | inr h' => simp [CmpTy, *]

theorem Ctx.CmpTy.univ_iff {Γ A B} (hAB : CmpTy Γ A B) : IsUniv Γ A ↔ IsUniv Γ B
  := by cases hAB with | inl h => exact IsUniv.eq_iff h | inr h => simp only [h]

theorem Ctx.SubTy.diamond {Γ A X Y} (hAX : SubTy Γ A X) (hAY : SubTy Γ A Y) : CmpTy Γ X Y :=
  .trans (.symm (.of_sub hAX)) (.of_sub hAY)

theorem Ctx.CmpTy.diamond {Γ A B} (h : CmpTy Γ A B) : ∃C, SubTy Γ A C ∧ SubTy Γ B C
  := by cases h with
  | inl h => exact ⟨B, .of_eq h, .refl h.rhs⟩
  | inr h =>
    have ⟨⟨m, hA⟩, ⟨n, hB⟩⟩ := h;
    exact ⟨.univ (m ⊔ n),
      .trans (.of_eq hA) (.univLE hA.ok (by simp)),
      .trans (.of_eq hB) (.univLE hA.ok (by simp))⟩

theorem Ctx.CmpTy.of_diamond {Γ A B C} (hA : SubTy Γ A C) (hB : SubTy Γ B C) : CmpTy Γ A B
  := .trans (.of_sub hA) (.symm (.of_sub hB))

theorem Ctx.CmpTy.diamond_iff {Γ A B} : CmpTy Γ A B ↔ ∃C, SubTy Γ A C ∧ SubTy Γ B C
  := ⟨diamond, fun ⟨_, ⟨h, h'⟩⟩ => of_diamond h h'⟩
