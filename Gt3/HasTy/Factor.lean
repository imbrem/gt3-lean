import Gt3.HasTy.Basic

inductive Ctx.InnerTy : Ctx → Tm 0 → Tm 0 → Prop
  | fv {Γ : Ctx} {x : String} {A : Tm 0} (hΓ : Ok Γ) (hA : Lookup Γ x A) : InnerTy Γ A (.fv x)
  | univ {Γ : Ctx} {ℓ} (hΓ : Ok Γ) : InnerTy Γ (.univ (ℓ + 1)) (.univ ℓ)
  | empty {Γ : Ctx} {ℓ} (hΓ : Ok Γ) : InnerTy Γ (.univ ℓ) .empty
  | unit {Γ : Ctx} {ℓ} (hΓ : Ok Γ) : InnerTy Γ (.univ ℓ) .unit
  | null {Γ : Ctx} (hΓ : Ok Γ) : InnerTy Γ .unit .null
  | eqn {Γ : Ctx} {A a b : Tm 0} {ℓ : ℕ}
    (ha : HasTy Γ A a) (hb : HasTy Γ A b)
    : InnerTy Γ (.univ ℓ) (.eqn a b)
  | pi {Γ : Ctx} {A : Tm 0} {B : Tm 1} {ℓ m n : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A) (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hm : m ≤ ℓ) (hn : n ≤ ℓ) (hℓ : 1 ≤ ℓ)
    : InnerTy Γ (.univ ℓ) (.pi A B)
  | abs {Γ : Ctx} {A : Tm 0} {B b : Tm 1} {m n : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A) (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hb : ∀ x ∉ L, HasTy (Γ.cons x A) (B.open x) (b.open x))
    : InnerTy Γ (A.pi B) (A.abs B b)
  | app {Γ : Ctx} {A : Tm 0} {B : Tm 1} {f a Ba : Tm 0}
    (hf : HasTy Γ (A.pi B) f) (ha : HasTy Γ A a)
    (hBa : TyEq Γ (B.lst a) Ba)
    : InnerTy Γ Ba (f.app a)

theorem Ctx.InnerTy.toTy {Γ A a} (h : InnerTy Γ A a) : HasTy Γ A a
  := by cases h <;> constructor <;> assumption

syntax "inner_ty_iff_tactic" : tactic

macro_rules
  | `(tactic| inner_ty_iff_tactic) => `(tactic| {
    constructor
    · intro x; cases x; simp [*]
    · intro x; (try casesm* (_ ∧ _), (∃_, _), (_ = _)); constructor <;> simp [*]
  })


theorem Ctx.InnerTy.fv_iff {Γ x A} : InnerTy Γ A (.fv x) ↔ Ok Γ ∧ Lookup Γ x A
  := by inner_ty_iff_tactic

theorem Ctx.InnerTy.univ_iff {Γ A ℓ} : InnerTy Γ A (.univ ℓ) ↔ Ok Γ ∧ A = (.univ (ℓ + 1))
  := by inner_ty_iff_tactic

theorem Ctx.InnerTy.empty_iff {Γ A} : InnerTy Γ A (.empty) ↔ Ok Γ ∧ ∃ℓ, A = (.univ ℓ)
  := by inner_ty_iff_tactic

theorem Ctx.InnerTy.unit_iff {Γ A} : InnerTy Γ A (.unit) ↔ Ok Γ ∧ ∃ℓ, A = (.univ ℓ)
  := by inner_ty_iff_tactic

theorem Ctx.InnerTy.null_iff {Γ A ℓ} : InnerTy Γ A (.univ ℓ) ↔ Ok Γ ∧ A = (.univ (ℓ + 1))
  := by inner_ty_iff_tactic

inductive Ctx.OuterTy : Ctx → Tm 0 → Tm 0 → Prop
| cast_level {Γ : Ctx} {ℓ A}
  (hA : OuterTy Γ (.univ ℓ) A)
  : OuterTy Γ (.univ (ℓ + 1)) A
| cast {Γ : Ctx} {A A' a : Tm 0}
  (hA : TyEq Γ A A') (ha : OuterTy Γ A a)
  : OuterTy Γ A' a
| base {Γ A a}
  (hA  : InnerTy Γ A a)
  : OuterTy Γ A a

theorem Ctx.OuterTy.toTy {Γ A a} (h : OuterTy Γ A a) : HasTy Γ A a := by induction h with
  | base hA => exact hA.toTy
  | _ => constructor <;> assumption

theorem Ctx.HasTy.factor {Γ A a} (h : HasTy Γ A a) : OuterTy Γ A a := by induction h with
  | cast_level => apply OuterTy.cast_level ; assumption
  | cast => apply OuterTy.cast <;> assumption
  | _ => apply OuterTy.base; constructor <;> assumption
