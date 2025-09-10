import Gt3.JEq.Basic

inductive Ctx.SSubTy : Ctx → Tm 0 → Tm 0 → Prop
  | refl {Γ A} (hA : IsTy Γ A) : SSubTy Γ A A
  | cast_level {Γ S ℓ} (hS : SSubTy Γ S (.univ ℓ)) : SSubTy Γ S (.univ (ℓ + 1))
  | cast {Γ S A A'} (hS : SSubTy Γ S A) (hA : TyEq Γ A A') : SSubTy Γ S A'

theorem Ctx.SSubTy.trans {Γ A B C} (hAB : SSubTy Γ A B) (hBC : SSubTy Γ B C) : SSubTy Γ A C
  := by induction hBC with
  | refl => assumption
  | _ => constructor <;> assumption

theorem Ctx.SSubTy.lhs {Γ A B} (h : SSubTy Γ A B) : IsTy Γ A := by induction h <;> assumption

theorem Ctx.SSubTy.ok {Γ A B} (h : SSubTy Γ A B) : Ok Γ := h.lhs.ok

theorem Ctx.SSubTy.rhs {Γ A B} (h : SSubTy Γ A B) : IsTy Γ B := by cases h with
  | refl h => exact h
  | cast_level h => exact .univ h.ok
  | cast _ h => exact h.rhs

theorem Ctx.SSubTy.of_eq {Γ A B} (h : TyEq Γ A B) : SSubTy Γ A B := (SSubTy.refl h.lhs).cast h

theorem Ctx.SSubTy.univ_mpr {Γ A U} (h : SSubTy Γ A U) (hU : IsUniv Γ U) : IsUniv Γ A
  := by induction h with
  | refl => assumption
  | cast_level h I => exact I (.univ h.ok)
  | cast h he I => exact I (hU.cast he)

theorem Ctx.SSubTy.univ_rhs {Γ A ℓ} (h : SSubTy Γ A (.univ ℓ)) : IsUniv Γ A
  := univ_mpr h (.univ h.ok)

theorem Ctx.SSubTy.univ_mp {Γ U B} (h : SSubTy Γ U B) (hU : IsUniv Γ U) : IsUniv Γ B
  := by induction h with
  | refl => assumption
  | cast_level h => exact .univ h.ok
  | cast h he I => exact I.cast he.symm

theorem Ctx.SSubTy.univ_lhs {Γ ℓ B} (h : SSubTy Γ (.univ ℓ) B) : IsUniv Γ B
  := univ_mp h (.univ h.ok)

theorem Ctx.SSubTy.univ_iff {Γ A B} (h : SSubTy Γ A B) : IsUniv Γ A ↔ IsUniv Γ B
  := ⟨h.univ_mp, h.univ_mpr⟩

theorem Ctx.SSubTy.univLE {Γ lo hi} (hΓ : Ok Γ) (h : lo ≤ hi) : SSubTy Γ (.univ lo) (.univ hi) := by
  induction h with
  | refl => exact .refl (.univ hΓ)
  | step _ I => exact I.cast_level

theorem Ctx.SSubTy.not_univ {Γ A B} (h : SSubTy Γ A B) (hB : ¬IsUniv Γ B) : TyEq Γ A B := by
  induction h with
  | refl h => exact h
  | cast_level h => exact (hB (.univ h.ok)).elim
  | cast _ h I =>
    apply TyEq.trans (I _) h
    rw [IsUniv.eq_iff h]
    exact hB

theorem Ctx.SSubTy.univ_or {Γ A B} (h : SSubTy Γ A B) : TyEq Γ A B  ∨ IsUniv Γ B  := by
  convert h.not_univ
  rw [or_iff_not_imp_right]

def Ctx.SCmpTy (Γ : Ctx) (A B : Tm 0) := TyEq Γ A B ∨ (IsUniv Γ A ∧ IsUniv Γ B)

theorem Ctx.SCmpTy.of_eq {Γ A B} (hAB : TyEq Γ A B) : SCmpTy Γ A B := .inl hAB

theorem Ctx.SCmpTy.refl {Γ A} (hA : IsTy Γ A) : SCmpTy Γ A A := .of_eq hA

theorem Ctx.SCmpTy.of_sub {Γ A B} (hAB : SSubTy Γ A B) : SCmpTy Γ A B := by
  cases hAB.univ_or <;> simp [hAB.univ_iff, SCmpTy, *]

theorem Ctx.SCmpTy.symm {Γ A B} (hAB : SCmpTy Γ A B) : SCmpTy Γ B A
  := by cases hAB with | inl h => exact .inl h.symm | inr h => simp [SCmpTy, *]

theorem Ctx.SCmpTy.trans {Γ A B C} (hAB : SCmpTy Γ A B) (hBC : SCmpTy Γ B C) : SCmpTy Γ A C := by
  cases hAB with
  | inl h => cases hBC with
    | inl h' => exact .inl (h.trans h')
    | inr h' => simp [SCmpTy, IsUniv.eq_iff h, *]
  | inr h => cases hBC with
  | inl h' => simp [SCmpTy, <-IsUniv.eq_iff ‹_›, *]
  | inr h' => simp [SCmpTy, *]

theorem Ctx.SCmpTy.univ_iff {Γ A B} (hAB : SCmpTy Γ A B) : IsUniv Γ A ↔ IsUniv Γ B
  := by cases hAB with | inl h => exact IsUniv.eq_iff h | inr h => simp only [h]

theorem Ctx.SSubTy.diamond {Γ A X Y} (hAX : SSubTy Γ A X) (hAY : SSubTy Γ A Y) : SCmpTy Γ X Y :=
  .trans (.symm (.of_sub hAX)) (.of_sub hAY)

theorem Ctx.SCmpTy.diamond {Γ A B} (h : SCmpTy Γ A B) : ∃C, SSubTy Γ A C ∧ SSubTy Γ B C
  := by cases h with
  | inl h => exact ⟨B, .of_eq h, .refl h.rhs⟩
  | inr h =>
    have ⟨⟨m, hA⟩, ⟨n, hB⟩⟩ := h;
    exact ⟨.univ (m ⊔ n),
      .trans (.of_eq hA) (.univLE hA.ok (by simp)),
      .trans (.of_eq hB) (.univLE hA.ok (by simp))⟩

theorem Ctx.SCmpTy.of_diamond {Γ A B C} (hA : SSubTy Γ A C) (hB : SSubTy Γ B C) : SCmpTy Γ A B
  := .trans (.of_sub hA) (.symm (.of_sub hB))

theorem Ctx.SCmpTy.diamond_iff {Γ A B} : SCmpTy Γ A B ↔ ∃C, SSubTy Γ A C ∧ SSubTy Γ B C
  := ⟨diamond, fun ⟨_, ⟨h, h'⟩⟩ => of_diamond h h'⟩
