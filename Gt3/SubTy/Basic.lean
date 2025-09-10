import Gt3.SubTy.Strict
import Gt3.JEq.Regular

inductive Ctx.SubTy : Ctx → Tm 0 → Tm 0 → Prop
  | refl {Γ A} (hA : IsTy Γ A) : SubTy Γ A A
  | pi {S Γ A B B'} {L : Finset String}
    (hS : SubTy Γ S (A.pi B))
    (hB : ∀ x ∉ L, SubTy (Γ.cons x A) (B.open x) (B'.open x))
    : SubTy Γ S (A.pi B')
  | cast_level {Γ S ℓ} (hS : SubTy Γ S (.univ ℓ)) : SubTy Γ S (.univ (ℓ + 1))
  | cast {Γ S A A'} (hS : SubTy Γ S A) (hA : TyEq Γ A A') : SubTy Γ S A'

theorem Ctx.SubTy.trans {Γ A B C} (hAB : SubTy Γ A B) (hBC : SubTy Γ B C) : SubTy Γ A C
  := by induction hBC with
  | refl => assumption
  | _ => constructor <;> apply_assumption; assumption

theorem Ctx.SubTy.lhs_is_ty {Γ A B} (h : SubTy Γ A B) : IsTy Γ A := by induction h <;> assumption

theorem Ctx.SubTy.lhs {Γ A B} (h : SubTy Γ A B) : SubTy Γ A A := .refl h.lhs_is_ty

theorem Ctx.SubTy.ok {Γ A B} (h : SubTy Γ A B) : Ok Γ := h.lhs_is_ty.ok

theorem Ctx.SubTy.rhs_is_ty {Γ A B} (h : SubTy Γ A B) : IsTy Γ B := by induction h with
  | refl h => exact h
  | pi _ _ _ IB => exact .pi IB
  | cast_level h => exact .univ h.ok
  | cast _ h => exact h.rhs

theorem Ctx.SubTy.rhs {Γ A B} (h : SubTy Γ A B) : SubTy Γ B B := .refl h.rhs_is_ty

theorem Ctx.SubTy.of_strict {Γ A B} (h : SSubTy Γ A B) : SubTy Γ A B
  := by induction h <;> constructor <;> assumption

theorem Ctx.SubTy.of_eq {Γ A B} (h : TyEq Γ A B) : SubTy Γ A B := .of_strict (.of_eq h)

theorem Ctx.SubTy.univLE {Γ lo hi} (hΓ : Ok Γ) (h : lo ≤ hi) : SubTy Γ (.univ lo) (.univ hi)
  := .of_strict (.univLE hΓ h)

def Ctx.CmpTy (Γ : Ctx) (A B : Tm 0) := ∃C, SubTy Γ A C ∧ SubTy Γ B C

theorem Ctx.CmpTy.refl {Γ A} (h : IsTy Γ A) : CmpTy Γ A A := ⟨A, .refl h, .refl h⟩

theorem Ctx.CmpTy.symm {Γ A B} (h : CmpTy Γ A B) : CmpTy Γ B A := have ⟨C, hl, hr⟩ := h; ⟨C, hr, hl⟩

theorem Ctx.CmpTy.lhs_is_ty {Γ A B} (h : CmpTy Γ A B) : IsTy Γ A
  := have ⟨_, hl, _⟩ := h; hl.lhs_is_ty

theorem Ctx.CmpTy.rhs_is_ty {Γ A B} (h : CmpTy Γ A B) : IsTy Γ B := h.symm.lhs_is_ty

inductive Ctx.GSubTy : ℕ → Ctx → Tm 0 → Tm 0 → Prop
  | pi {s} {S Γ A B B'} {L : Finset String}
    (hS : GSubTy s Γ S (A.pi B))
    (hB : ∀ x ∉ L, GSubTy s (Γ.cons x A) (B.open x) (B'.open x))
    : GSubTy (s + 1) Γ S (A.pi B')
  | cast_level {s Γ S ℓ} (hS : GSubTy s Γ S (.univ ℓ)) : GSubTy (s + 1) Γ S (.univ (ℓ + 1))
  | trans {s Γ A B C} (hS : GSubTy s Γ A B) (hA : GSubTy s Γ B C) : GSubTy (s + 1) Γ A C
  | of_eq {s Γ A B} (hA : TyEq Γ A B) : GSubTy s Γ A B

theorem Ctx.GSubTy.step {s} {Γ A B} (h : GSubTy s Γ A B) : GSubTy (s + 1) Γ A B
  := by induction h with
  | of_eq => apply of_eq; assumption
  | _ => constructor <;> assumption

theorem Ctx.GSubTy.mono {lo hi} (h : lo ≤ hi) {Γ A B} (hΓ : GSubTy lo Γ A B) : GSubTy hi Γ A B
  := by induction h with
  | refl => exact hΓ
  | step _ I => exact I.step

theorem Ctx.GSubTy.castIn {s Γ A B C} (hAB : TyEq Γ A B) (hBC : GSubTy s Γ B C) : GSubTy s Γ A C
  := by induction hBC with
  | of_eq hBC => exact .of_eq (hAB.trans hBC)
  | pi _ hB I => exact .pi (I hAB) hB
  | cast_level _ I => exact cast_level (I hAB)
  | trans _ hB IA IB => exact trans (IA hAB) hB


theorem Ctx.GSubTy.erase {s Γ A B} (h : GSubTy s Γ A B) : SubTy Γ A B := by induction h with
  | of_eq h => exact .of_eq h
  | trans => apply SubTy.trans <;> assumption
  | _ => constructor <;> assumption

theorem Ctx.GSubTy.lhs_is_ty {s Γ A B} (h : GSubTy s Γ A B) : IsTy Γ A := h.erase.lhs_is_ty

theorem Ctx.GSubTy.ok {s Γ A B} (h : GSubTy s Γ A B) : Ok Γ := h.lhs_is_ty.ok

theorem Ctx.GSubTy.rhs_is_ty {s Γ A B} (h : GSubTy s Γ A B) : IsTy Γ B := h.erase.rhs_is_ty

def Ctx.GCmpTy (s : ℕ) (Γ : Ctx) (A B : Tm 0) := ∃C, GSubTy s Γ A C ∧ GSubTy s Γ B C

theorem Ctx.GCmpTy.of_eq {s Γ A B} (h : TyEq Γ A B) : GCmpTy s Γ A B := ⟨B, .of_eq h, .of_eq h.rhs⟩

theorem Ctx.GCmpTy.symm {s Γ A B} (h : GCmpTy s Γ A B) : GCmpTy s Γ B A
  := have ⟨C, hl, hr⟩ := h; ⟨C, hr, hl⟩

theorem Ctx.GCmpTy.of_sub {s Γ A B} (h : GSubTy s Γ A B) : GCmpTy s Γ A B
  := ⟨B, h, .of_eq h.rhs_is_ty⟩

-- theorem Ctx.GSubTy.diamond_max
--   {sX sY Γ A X Y} (hX : GSubTy sX Γ A X) (hY : GSubTy sY Γ A Y) : GCmpTy (sX ⊔ sY) Γ X Y
--   := by induction sX generalizing hY Γ A X Y with
--   | zero => cases hX with | of_eq hX => convert GCmpTy.of_sub (hY.castIn hX.symm); simp
--   | succ s I =>
--     cases hX with
--     | of_eq hX => sorry
--     | pi => sorry
--     | cast_level => sorry
--     | trans hX₁ hX₂ =>
--       sorry
