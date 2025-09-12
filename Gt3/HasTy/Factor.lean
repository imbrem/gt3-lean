import Gt3.HasTy.Regular

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
  | app' {Γ : Ctx} {A : Tm 0} {B : Tm 1} {f a Ba : Tm 0} {m n : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A) (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hf : HasTy Γ (A.pi B) f) (ha : HasTy Γ A a)
    (hBa : TyEq Γ (B.lst a) Ba)
    : InnerTy Γ Ba (f.app a)
  | sigma {Γ : Ctx} {A : Tm 0} {B : Tm 1} {ℓ m n : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A) (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hm : m ≤ ℓ) (hn : n ≤ ℓ) (hℓ : 1 ≤ ℓ)
    : InnerTy Γ (.univ ℓ) (.sigma A B)
  | fst' {Γ : Ctx}  {A : Tm 0} {B : Tm 1} {p : Tm 0} {m n : ℕ} {L : Finset String}
    (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hA : HasTy Γ (.univ m) A)
    (hp : HasTy Γ (.sigma A B) p)
    : InnerTy Γ A (.fst p)
  | pair {Γ : Ctx} {A a b : Tm 0} {B : Tm 1} {m n : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A) (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (ha : HasTy Γ A a) (hb : HasTy Γ (B.lst a) b)
    : InnerTy Γ (.sigma A B) (.pair a b)

theorem Ctx.InnerTy.has_ty {Γ A a} (h : InnerTy Γ A a) : HasTy Γ A a
  := by cases h <;> constructor <;> assumption

theorem Ctx.InnerTy.is_wf {Γ A a} (h : InnerTy Γ A a) : IsWf Γ a := h.has_ty.is_wf

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
| transfer {Γ : Ctx} {A B a : Tm 0}
  (hA : OuterTy Γ A a) (hB : JEq Γ B a a)
  : OuterTy Γ B a
| base {Γ A a}
  (hA  : InnerTy Γ A a)
  : OuterTy Γ A a

theorem Ctx.OuterTy.has_ty {Γ A a} (h : OuterTy Γ A a) : HasTy Γ A a := by induction h with
  | base hA => exact hA.has_ty
  | transfer => apply HasTy.transfer <;> assumption
  | _ => constructor <;> assumption

theorem Ctx.OuterTy.is_wf {Γ A a} (h : OuterTy Γ A a) : IsWf Γ a := h.has_ty.is_wf

theorem Ctx.HasTy.factor {Γ A a} (h : HasTy Γ A a) : OuterTy Γ A a := by induction h with
  | cast_level => apply OuterTy.cast_level ; assumption
  | cast => apply OuterTy.cast <;> assumption
  | transfer => apply OuterTy.transfer <;> assumption
  | _ => apply OuterTy.base; constructor <;> assumption

theorem Ctx.OuterTy.iff_has_ty {Γ A a} : OuterTy Γ A a ↔ HasTy Γ A a := ⟨has_ty, HasTy.factor⟩

theorem Ctx.OuterTy.inner_ty {Γ A a} (h : OuterTy Γ A a) : ∃W, InnerTy Γ W a := by induction h with
  | base hA => exact ⟨_, hA⟩
  | _ => assumption

theorem Ctx.HasTy.inner_ty {Γ A a} (h : HasTy Γ A a) : ∃W, InnerTy Γ W a := h.factor.inner_ty

theorem Ctx.IsWf.inner_ty {Γ a} (h : IsWf Γ a) : ∃W, InnerTy Γ W a
  := have ⟨_, h⟩ := h.has_ty; h.inner_ty

theorem Ctx.IsWf.iff_inner_ty {Γ a} : IsWf Γ a ↔ ∃W, InnerTy Γ W a
  := ⟨inner_ty, fun ⟨_, h⟩ => h.is_wf⟩

theorem Ctx.JEq.app {Γ} {A : Tm 0} {B : Tm 1} {f a f' a' Ba : Tm 0}
  (hf : JEq Γ (A.pi B) f f') (ha : JEq Γ A a a') (hBa : TyEq Γ (B.lst a) Ba)
  : JEq Γ Ba (f.app a) (f'.app a') := by
  have ⟨_, hpi⟩ := hf.regular;
  have ⟨_, hpi⟩ := hpi.lhs_ty.inner_ty;
  cases hpi with
  | pi hA hB => exact .app_f (fun x hx => (hB x hx).refl) hA.refl hf ha hBa

syntax "jeq_congr" : tactic

macro_rules
  | `(tactic| jeq_congr_f) => `(tactic| first
    | apply Ctx.JEq.fv
    | apply Ctx.JEq.univ
    | apply Ctx.JEq.empty
    | apply Ctx.JEq.unit
    | apply Ctx.JEq.null
    | apply Ctx.JEq.eqn
    | apply Ctx.JEq.pi
    | apply Ctx.JEq.abs
    | apply Ctx.JEq.app
    | apply Ctx.JEq.sigma
  )
