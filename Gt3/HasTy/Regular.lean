import Gt3.HasTy.Subst
import Gt3.JEq.Lsv

namespace Gt3

def Ctx.HasTy.regular {Γ A a} (h : HasTy Γ A a) : IsTy Γ A := h.refl.regular

theorem Ctx.HasTy.lst_cf_cast {Γ : Ctx} {ℓ A a a' b} {B B' : Tm 1} {L : Finset String}
  (hB : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (.univ ℓ) (B.open x) (B'.open x))
  (ha : JEq Γ A a a')
  (hBa : HasTy Γ (B.lst a) b)
  : HasTy Γ (B.lst a') b
  := hBa.cast (IsTy.lst_cf' (fun x hx => (hB x hx).lhs_is_ty) ha)

def Ctx.Cmp (Γ : Ctx) (A a b : Tm 0) : Prop := HasTy Γ A a ∧ HasTy Γ A b

theorem Ctx.Cmp.cast_level {Γ ℓ A B} (h : Cmp Γ (.univ ℓ) A B) : Cmp Γ (.univ (ℓ + 1)) A B
  := ⟨h.left.cast_level, h.right.cast_level⟩

theorem Ctx.Cmp.cast' {Γ ℓ A A' a b} (hA : JEq Γ (.univ ℓ) A A') (hab : Cmp Γ A a b)
  : Cmp Γ A' a b := ⟨hab.left.cast' hA, hab.right.cast' hA⟩

theorem Ctx.Cmp.symm {Γ A a b} (h : Cmp Γ A a b) : Cmp Γ A b a
  := ⟨h.right, h.left⟩

theorem Ctx.Cmp.trans {Γ A a b c} (h : Cmp Γ A a b) (h' : Cmp Γ A b c) : Cmp Γ A a c
  := ⟨h.left, h'.right⟩

theorem Ctx.Cmp.of_both {Γ A a b} (h : Cmp Γ A a a) (h' : Cmp Γ A b b) : Cmp Γ A a b
  := ⟨h.left, h'.right⟩

theorem Ctx.Cmp.of_cast {Γ A B a b}
  (ha : HasTy Γ A a) (hb : HasTy Γ B b) (hAB : TyEq Γ A B) : Cmp Γ A a b
  := ⟨ha, hb.cast hAB.symm⟩

theorem Ctx.HasTy.succArrow_cast {Γ : Ctx} {ℓ} {C C' s : Tm 1} {L : Finset String}
  (hC : ∀ x ∉ L, Ctx.JEq (Γ.cons x .nats) (.univ ℓ) (C.open x) (C'.open x))
  (hs : ∀ x ∉ L, Ctx.HasTy (Γ.cons x .nats) ((Tm.succArrow C).open x) (s.open x))
  : ∀ x ∉ L, Ctx.HasTy (Γ.cons x .nats) ((Tm.succArrow C').open x) (s.open x)
  := fun x hx => (hs x hx).cast (TyEq.succArrow' hC x hx)

theorem Ctx.HasTy.lst_cast {Γ : Ctx} {ℓ} {A a a' b : Tm 0} {B B' : Tm 1} {L : Finset String}
  (hB : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (.univ ℓ) (B.open x) (B'.open x))
  (ha : Ctx.JEq Γ A a a')
  (hb : Ctx.HasTy Γ (B.lst a) b)
  : Ctx.HasTy Γ (B'.lst a') b
  := hb.cast (TyEq.lst_cf (fun x hx => (hB x hx).ty_eq) ha)

theorem Ctx.HasTy.lst_cast_zero {Γ : Ctx} {ℓ} {b : Tm 0} {B B' : Tm 1} {L : Finset String}
  (hB : ∀ x ∉ L, Ctx.JEq (Γ.cons x .nats) (.univ ℓ) (B.open x) (B'.open x))
  (hb : Ctx.HasTy Γ (B.lst .zero) b)
  : Ctx.HasTy Γ (B'.lst .zero) b
  := hb.lst_cast hB (.zero hb.ok)

theorem Ctx.JEq.cmp {Γ A a b} (h : JEq Γ A a b) : Cmp Γ A a b := by induction h with
  | nil_ok | cons_ok =>
      constructor <;> constructor <;> constructor
      <;> first | assumption | apply JEq.ok; assumption | apply JEq.lhs_is_ty; assumption
  | cast' => apply Cmp.cast' <;> assumption
  | transfer' hA hB IA IB => exact ⟨IB.right, IA.right.transfer (hA.transfer' hB.rhs_ty').rhs_ty'⟩
  | _ =>
    simp only [Ctx.Cmp, forall_and] at *
    casesm* _ ∧ _
    first
    | {
      -- Rewrite rules and simple cases
      apply And.intro <;>
      first
      | assumption
      | {
          constructor <;> first
          | assumption
          | apply Ctx.JEq.ok ; assumption
          | intros; apply HasTy.cast_top_symm' <;> apply_assumption; assumption
        }
    }
    | {
      -- Cases with binding
      apply Cmp.of_cast
      · constructor
        <;> first | assumption | apply JEq.ty_eq; assumption
      · constructor <;> first
        | assumption
        | intros; apply HasTy.cast_top_symm' <;> apply_assumption; assumption
        | intros; apply HasTy.cast_top_not_symm' <;> apply_assumption; assumption
        | {
          apply Ctx.IsInhab.cast
          · apply JEq.ty_eq; assumption
          · apply JEq.inhab_def; assumption
        }
        --| intros; apply HasTy.cast_top_symm₂ <;> apply_assumption <;> assumption
        | apply Ctx.HasTy.lst_cf_cast <;> assumption
        | apply Ctx.HasTy.cast' <;> assumption
        | apply Ctx.HasTy.succArrow_cast <;> assumption
        | apply Ctx.HasTy.lst_cast_zero <;> assumption
        | apply Ctx.JEq.lst_cf_cast_ty <;> first | assumption
                                                  | apply Ctx.JEq.lhs_is_ty; assumption
                                                  | apply Ctx.JEq.fst' <;> assumption
      · first
        | apply JEq.ty_eq; assumption
        | apply TyEq.symm; apply JEq.ty_eq; assumption
        | (ty_eq_constructor'
          <;> intros
          <;> first | exact L | apply JEq.ty_eq <;> apply_assumption <;> assumption
                              | apply HasTy.is_ty; apply_assumption; assumption
                              | apply JEq.ok <;> assumption
          )
    }

theorem Ctx.JEq.lhs_ty {Γ A a b} (h : JEq Γ A a b) : HasTy Γ A a := h.cmp.left

theorem Ctx.JEq.rhs_ty {Γ A a b} (h : JEq Γ A a b) : HasTy Γ A b := h.cmp.right

theorem Ctx.HasTy'.has_ty {Γ A a} (h : HasTy' Γ A a) : HasTy Γ A a := JEq.lhs_ty h

theorem Ctx.HasTy'.def_has_ty {Γ A a} : HasTy' Γ A a ↔ HasTy Γ A a := ⟨has_ty, HasTy.refl⟩

theorem Ctx.JEq.refl_iff {Γ A a} : JEq Γ A a a ↔ HasTy Γ A a := HasTy'.def_has_ty

theorem Ctx.JEq.has_ty_mp {Γ A B a b} (h : JEq Γ A a b) (hB : HasTy Γ B a) : HasTy Γ B b
  := (h.ltr hB).rhs_ty

theorem Ctx.JEq.has_ty_iff {Γ A a b} (h : JEq Γ A a b) : ∀{B}, HasTy Γ B a ↔ HasTy Γ B b
  := ⟨h.has_ty_mp, h.symm.has_ty_mp⟩

theorem Ctx.IsWf.has_ty_def {Γ a} : IsWf Γ a ↔ ∃A, HasTy Γ A a
  := by simp only [IsWf, WfEq, JEq.refl_iff]

theorem Ctx.IsWf.has_ty {Γ a} (h : IsWf Γ a) : ∃A, HasTy Γ A a := has_ty_def.mp h

theorem Ctx.IsTy.def_has_ty {Γ A} : IsTy Γ A ↔ ∃ℓ, HasTy Γ (.univ ℓ) A := by
  simp only [IsTy, TyEq, <-JEq.refl_iff]

theorem Ctx.IsTy.has_ty {Γ A} (h : IsTy Γ A) : ∃ℓ, HasTy Γ (.univ ℓ) A := IsTy.def_has_ty.mp h

theorem Ctx.HasTy.m_has_ty {Γ A a} (h : HasTy Γ A a) : HasTy Γ (.univ 0) (.has_ty A a)
  := have ⟨_, hA⟩ := h.regular.has_ty; .m_has_ty' hA h

theorem Ctx.HasTy.inhab {Γ A a} (h : HasTy Γ A a) : IsInhab Γ A := h.refl.inhab

theorem Ctx.HasTy.abs {Γ A} {B b : Tm 1} {L : Finset String}
  (hb : ∀ x ∉ L, HasTy (Γ.cons x A) (B.open x) (b.open x))
  : HasTy Γ (.pi A B) (.abs A b)
  :=
  have ⟨x, hx⟩ := L.exists_notMem;
  have ⟨_, hA⟩ := (hb x hx).ok.ty;
  have ⟨_, hB⟩ := IsTy.max_univ' (fun x hx => (hb x hx).regular);
  HasTy.abs' hA.lhs_ty (fun x hx => (hB x hx).lhs_ty) hb

theorem Ctx.HasTy.pair {Γ} {A a b : Tm 0} {B : Tm 1} {n : ULevel} {L : Finset String}
    (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (ha : HasTy Γ A a) (hb : HasTy Γ (B.lst a) b)
    : HasTy Γ (.sigma A B) (.pair a b) :=
    have ⟨_, hA⟩ := ha.regular.has_ty;
    .pair' hA hB ha hb

-- theorem Ctx.HasTy.choose {Γ} {A : Tm 0} {φ : Tm 1} {ℓ : ℕ} {L : Finset String}
--     (hAI : IsInhab Γ A)
--     (hφ : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ 0) (φ.open x))
--     : HasTy Γ A (.choose A φ)
--     :=
--     have ⟨_, hA⟩ := hAI.is_ty;
--     .choose' hA hAI hφ

theorem Ctx.HasTy.lsv {Γ : Ctx} {A B a b : Tm 0} {x : String}
  (hb : Ctx.HasTy (Γ.cons x A) B b) (ha : Ctx.HasTy Γ A a)
  : Γ.HasTy (B.lsv x a) (b.lsv x a)
  := (hb.refl.lsv₁ ha.refl).lhs_ty

theorem Ctx.HasTy.lst_exact {Γ : Ctx} {A a : Tm 0} {B b : Tm 1} {x : String}
  (hx : x ∉ B.fvs ∪ b.fvs)
  (hb : Ctx.HasTy (Γ.cons x A) (B.open x) (b.open x))
  (ha : Ctx.HasTy Γ A a) : Γ.HasTy (B.lst a) (b.lst a)
  := (hb.refl.lst₁ (by convert hx using 0; simp) ha.refl).lhs_ty

theorem Ctx.HasTy.lst {Γ : Ctx} {A a : Tm 0} {B b : Tm 1} {L : Finset String}
  (hb : ∀ x ∉ L, Ctx.HasTy (Γ.cons x A) (B.open x) (b.open x))
  (ha : Ctx.HasTy Γ A a) : Γ.HasTy (B.lst a) (b.lst a) := by
  have ⟨x, hx⟩ := (L ∪ (B.fvs) ∪ b.fvs).exists_notMem;
  simp at hx
  exact HasTy.lst_exact (by simp [hx]) (hb x (by simp [hx])) ha

end Gt3
