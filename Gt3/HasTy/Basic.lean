import Gt3.JEq.Basic

inductive Ctx.HasTy : Ctx → Tm 0 → Tm 0 → Prop
  | fv {Γ : Ctx} {x : String} {A : Tm 0} (hΓ : Ok Γ) (hA : Lookup Γ x A) : HasTy Γ A (.fv x)
  | univ {Γ : Ctx} {ℓ} (hΓ : Ok Γ) : HasTy Γ (.univ (ℓ + 1)) (.univ ℓ)
  | empty {Γ : Ctx} {ℓ} (hΓ : Ok Γ) : HasTy Γ (.univ ℓ) .empty
  | unit {Γ : Ctx} {ℓ} (hΓ : Ok Γ) : HasTy Γ (.univ ℓ) .unit
  | eqn {Γ : Ctx} {A a b : Tm 0} {ℓ : ℕ}
    (ha : HasTy Γ A a) (hb : HasTy Γ A b)
    : HasTy Γ (.univ ℓ) (.eqn a b)
  | pi {Γ : Ctx} {A : Tm 0} {B : Tm 1} {ℓ m n : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A) (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hm : m ≤ ℓ) (hn : n ≤ ℓ) (hℓ : 1 ≤ ℓ)
    : HasTy Γ (.univ ℓ) (.pi A B)
  | abs {Γ : Ctx} {A : Tm 0} {B b : Tm 1} {m : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A)
    (hb : ∀ x ∉ L, HasTy (Γ.cons x A) (B.open x) (b.open x))
    : HasTy Γ (A.pi B) (A.abs b)
  | app {Γ : Ctx} {A : Tm 0} {B : Tm 1} {f a Ba : Tm 0}
    (hf : HasTy Γ (A.pi B) f) (ha : HasTy Γ A a)
    (hBa : TyEq Γ (B.lst a) Ba)
    : HasTy Γ Ba (f.app a)
  | cast_level {Γ : Ctx} {ℓ A}
    (hA : HasTy Γ (.univ ℓ) A)
    : HasTy Γ (.univ (ℓ + 1)) A
  | cast {Γ : Ctx} {A A' a : Tm 0}
    (hA : TyEq Γ A A') (ha : HasTy Γ A a)
    : HasTy Γ A' a

theorem Ctx.HasTy.cast' {Γ ℓ A A' a} (hA : JEq Γ (.univ ℓ) A A') (ha : HasTy Γ A a)
  : HasTy Γ A' a := .cast hA.ty_eq ha

theorem Ctx.HasTy.ok {Γ A a} (h : HasTy Γ A a) : Ok Γ := by induction h <;> assumption

theorem Ctx.HasTy.refl {Γ A a} (h : HasTy Γ A a) : JEq Γ A a a := by induction h with
  | cast_level _ IA => exact IA.cast_level
  | cast hA _ Ia => exact Ia.cast hA
  | _ => jeq_congr <;> assumption

theorem Ctx.HasTy.is_ty {Γ ℓ A} (h : HasTy Γ (.univ ℓ) A) : IsTy Γ A := h.refl.lhs_is_ty

def Ctx.Cmp (Γ : Ctx) (A a b : Tm 0) : Prop := HasTy Γ A a ∧ HasTy Γ A b

theorem Ctx.Cmp.cast_level {Γ ℓ A B} (h : Cmp Γ (.univ ℓ) A B) : Cmp Γ (.univ (ℓ + 1)) A B
  := ⟨h.left.cast_level, h.right.cast_level⟩

theorem Ctx.Cmp.cast' {Γ ℓ A A' a b} (hA : JEq Γ (.univ ℓ) A A') (hab : Cmp Γ A a b)
  : Cmp Γ A' a b := ⟨hab.left.cast' hA, hab.right.cast' hA⟩

theorem Ctx.Cmp.symm {Γ A a b} (h : Cmp Γ A a b) : Cmp Γ A b a
  := ⟨h.right, h.left⟩

theorem Ctx.Cmp.trans {Γ A a b c} (h : Cmp Γ A a b) (h' : Cmp Γ A b c) : Cmp Γ A a c
  := ⟨h.left, h'.right⟩

-- theorem Ctx.JEq.cmp {Γ A a b} (h : JEq Γ A a b) : Cmp Γ A a b := by induction h with
--   | nil_ok => sorry
--   | cons_ok => sorry
--   | cast_level => apply Cmp.cast_level; assumption
--   | cast' => apply Cmp.cast' <;> assumption
--   | symm => apply Cmp.symm; assumption
--   | trans => apply Cmp.trans <;> assumption
--   | _ =>
--     simp only [Ctx.Cmp, forall_and] at *
--     casesm* _ ∧ _
--     apply And.intro <;>
--     first
--     | assumption
--     | {
--         constructor <;> first
--         | assumption
--         | (apply Ctx.JEq.ok ; assumption)
--         | intros <;> apply JEq.cast_top' <;> apply_assumption
--         | sorry
--       }
