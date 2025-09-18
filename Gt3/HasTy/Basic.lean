import Gt3.JEq.Basic

inductive Ctx.HasTy : Ctx → Tm 0 → Tm 0 → Prop
  | fv {Γ} {x : String} {A : Tm 0} (hΓ : Ok Γ) (hA : Lookup Γ x A) : HasTy Γ A (.fv x)
  | univ {Γ} {ℓ} (hΓ : Ok Γ) : HasTy Γ (.univ (ℓ + 1)) (.univ ℓ)
  | empty {Γ} {ℓ} (hΓ : Ok Γ) : HasTy Γ (.univ ℓ) .empty
  | unit {Γ} {ℓ} (hΓ : Ok Γ) : HasTy Γ (.univ ℓ) .unit
  | null {Γ} (hΓ : Ok Γ) : HasTy Γ .unit .null
  | eqn {Γ} {A a b : Tm 0} {ℓ : ℕ}
    (ha : HasTy Γ A a) (hb : HasTy Γ A b)
    : HasTy Γ (.univ ℓ) (.eqn a b)
  | pi {Γ} {A : Tm 0} {B : Tm 1} {ℓ m n : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A) (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hm : m ≤ ℓ) (hn : n ≤ ℓ) (hℓ : 1 ≤ ℓ)
    : HasTy Γ (.univ ℓ) (.pi A B)
  | abs {Γ} {A : Tm 0} {B b : Tm 1} {m n : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A)
    (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hb : ∀ x ∉ L, HasTy (Γ.cons x A) (B.open x) (b.open x))
    : HasTy Γ (A.pi B) (A.abs b)
  | app' {Γ} {A : Tm 0} {B : Tm 1} {f a Ba : Tm 0} {m n : ℕ} {L : Finset String}
    (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hA : HasTy Γ (.univ m) A)
    (hf : HasTy Γ (A.pi B) f) (ha : HasTy Γ A a)
    (hBa : TyEq Γ (B.lst a) Ba)
    : HasTy Γ Ba (f.app a)
  | sigma {Γ} {A : Tm 0} {B : Tm 1} {ℓ m n : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A) (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hm : m ≤ ℓ) (hn : n ≤ ℓ) (hℓ : 1 ≤ ℓ)
    : HasTy Γ (.univ ℓ) (.sigma A B)
  | pair {Γ} {A a b : Tm 0} {B : Tm 1} {m n : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A) (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (ha : HasTy Γ A a) (hb : HasTy Γ (B.lst a) b)
    : HasTy Γ (.sigma A B) (.pair a b)
  | fst' {Γ}  {A : Tm 0} {B : Tm 1} {p : Tm 0} {m n : ℕ} {L : Finset String}
    (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hA : HasTy Γ (.univ m) A)
    (hp : HasTy Γ (.sigma A B) p)
    : HasTy Γ A (.fst p)
  | snd' {Γ}  {A : Tm 0} {B : Tm 1} {p Ba : Tm 0} {m n : ℕ} {L : Finset String}
    (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hA : HasTy Γ (.univ m) A)
    (hp : HasTy Γ (.sigma A B) p)
    (hBa : TyEq Γ (B.lst (.fst p)) Ba)
    : HasTy Γ Ba (.snd p)
  | dite' {Γ} {φ A : Tm 0} {l r : Tm 1} {ℓ : ℕ} {L : Finset String}
    (hφ : HasTy Γ (.univ 0) φ)
    (hA : HasTy Γ (.univ ℓ) A)
    (hl : ∀ x ∉ L, HasTy (Γ.cons x φ) A (l.open x))
    (hr : ∀ x ∉ L, HasTy (Γ.cons x φ.not) A (r.open x))
    : HasTy Γ A (.dite φ l r)
  | trunc {Γ} {A : Tm 0} {ℓ : ℕ}
    (hA : HasTy Γ (.univ ℓ) A)
    : HasTy Γ (.univ 0) (.trunc A)
  | choose' {Γ} {A : Tm 0} {φ : Tm 1} {ℓ : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ ℓ) A)
    (hAI : IsInhab Γ A)
    (hφ : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ 0) (φ.open x))
    : HasTy Γ A (.choose A φ)
  | nats {Γ} (hΓ : Ok Γ) : HasTy Γ (.univ 1) .nats
  | zero {Γ} (hΓ : Ok Γ) : HasTy Γ .nats .zero
  | succ {Γ} {n} (hn : HasTy Γ .nats n) : HasTy Γ .nats (.succ n)
  | natrec {Γ ℓ C s z n Cn} {L : Finset String}
    (hC : ∀x ∉ L, HasTy (Γ.cons x .nats)
                    (.univ ℓ) (C.open x))
    (hs : ∀x ∉ L, HasTy (Γ.cons x .nats) ((Tm.succArrow C).open x) (s.open x))
    (hz : HasTy Γ (C.lst .zero) z)
    (hn : HasTy Γ .nats n)
    (hCn : TyEq Γ (C.lst n) Cn)
    : HasTy Γ Cn (.natrec C s z n)
  | cast_level {Γ} {ℓ A}
    (hA : HasTy Γ (.univ ℓ) A)
    : HasTy Γ (.univ (ℓ + 1)) A
  | cast {Γ} {A A' a : Tm 0}
    (hA : TyEq Γ A A') (ha : HasTy Γ A a)
    : HasTy Γ A' a
  | transfer {Γ} {A B a : Tm 0}
    (hA : HasTy Γ A a) (hB : JEq Γ B a a)
    : HasTy Γ B a

theorem Ctx.HasTy.cast' {Γ ℓ A A' a} (hA : JEq Γ (.univ ℓ) A A') (ha : HasTy Γ A a)
  : HasTy Γ A' a := .cast hA.ty_eq ha

theorem Ctx.HasTy.ok {Γ A a} (h : HasTy Γ A a) : Ok Γ := by induction h <;> assumption

theorem Ctx.HasTy.not {Γ φ} (hφ : HasTy Γ (.univ 0) φ) : HasTy Γ (.univ 0) φ.not
  := .eqn hφ (.empty hφ.ok)

theorem Ctx.HasTy.refl {Γ A a} (h : HasTy Γ A a) : JEq Γ A a a := by induction h with
  | cast_level _ IA => exact IA.cast_level
  | cast hA _ Ia => exact Ia.cast hA
  | transfer _ hB IA => exact IA.transfer' hB
  | _ => jeq_congr_f <;> assumption

theorem Ctx.HasTy.is_wf {Γ A a} (h : HasTy Γ A a) : IsWf Γ a := h.refl.lhs_is_wf

theorem Ctx.HasTy.scoped_all {Γ A a} (h : HasTy Γ A a)
  : Scoped Γ ∧ A.fvs ⊆ Γ.dv ∧ a.fvs ⊆ Γ.dv := by simp [h.refl.scoped_all]

theorem Ctx.HasTy.is_ty {Γ ℓ A} (h : HasTy Γ (.univ ℓ) A) : IsTy Γ A := h.refl.lhs_is_ty

theorem Ctx.HasTy.top_var {Γ : Ctx} {x A} (h : Ok (Γ.cons x A)) : HasTy (Γ.cons x A) A (.fv x)
  := .fv h (.here _ _ _)

theorem Ctx.HasTy.top_var_iff {Γ : Ctx} {x A}
  : HasTy (Γ.cons x A) A (.fv x) ↔ Ok (Γ.cons x A)
  := ⟨HasTy.ok, HasTy.top_var⟩

theorem Ctx.JEq.ltr {Γ A B a b} (hA : JEq Γ A a b) (hB : HasTy Γ B a) : JEq Γ B a b
  := .transfer' hA hB.refl

theorem Ctx.JEq.rtr {Γ A B a b} (hA : JEq Γ A a b) (hB : HasTy Γ B b) : JEq Γ B a b
  := .symm (.ltr hA.symm hB)

theorem Ctx.WfEq.ltr {Γ A a b} (hab : WfEq Γ a b) (hA : HasTy Γ A a) : JEq Γ A a b
  := have ⟨_, hab⟩ := hab; hab.ltr hA

theorem Ctx.WfEq.rtr {Γ A a b} (hab : WfEq Γ a b) (hA : HasTy Γ A b) : JEq Γ A a b
  := have ⟨_, hab⟩ := hab; hab.rtr hA
