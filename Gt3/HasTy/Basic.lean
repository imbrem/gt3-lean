import Gt3.JEq.Basic

inductive Ctx.HasTy : Ctx → Tm 0 → Tm 0 → Prop
  | fv {Γ : Ctx} {x : String} {A : Tm 0} (hΓ : Ok Γ) (hA : Lookup Γ x A) : HasTy Γ A (.fv x)
  | univ {Γ : Ctx} {ℓ} (hΓ : Ok Γ) : HasTy Γ (.univ (ℓ + 1)) (.univ ℓ)
  | empty {Γ : Ctx} {ℓ} (hΓ : Ok Γ) : HasTy Γ (.univ ℓ) .empty
  | unit {Γ : Ctx} {ℓ} (hΓ : Ok Γ) : HasTy Γ (.univ ℓ) .unit
  | null {Γ : Ctx} (hΓ : Ok Γ) : HasTy Γ .unit .null
  | eqn {Γ : Ctx} {A a b : Tm 0} {ℓ : ℕ}
    (ha : HasTy Γ A a) (hb : HasTy Γ A b)
    : HasTy Γ (.univ ℓ) (.eqn a b)
  | pi {Γ : Ctx} {A : Tm 0} {B : Tm 1} {ℓ m n : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A) (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hm : m ≤ ℓ) (hn : n ≤ ℓ) (hℓ : 1 ≤ ℓ)
    : HasTy Γ (.univ ℓ) (.pi A B)
  | abs {Γ : Ctx} {A : Tm 0} {B b : Tm 1} {m n : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A)
    (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hb : ∀ x ∉ L, HasTy (Γ.cons x A) (B.open x) (b.open x))
    : HasTy Γ (A.pi B) (A.abs B b)
  | app' {Γ : Ctx} {A : Tm 0} {B : Tm 1} {f a Ba : Tm 0} {m n : ℕ} {L : Finset String}
    (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hA : HasTy Γ (.univ m) A)
    (hf : HasTy Γ (A.pi B) f) (ha : HasTy Γ A a)
    (hBa : TyEq Γ (B.lst a) Ba)
    : HasTy Γ Ba (f.app a)
  | sigma {Γ : Ctx} {A : Tm 0} {B : Tm 1} {ℓ m n : ℕ} {L : Finset String}
    (hA : HasTy Γ (.univ m) A) (hB : ∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.open x))
    (hm : m ≤ ℓ) (hn : n ≤ ℓ) (hℓ : 1 ≤ ℓ)
    : HasTy Γ (.univ ℓ) (.sigma A B)
  | cast_level {Γ : Ctx} {ℓ A}
    (hA : HasTy Γ (.univ ℓ) A)
    : HasTy Γ (.univ (ℓ + 1)) A
  | cast {Γ : Ctx} {A A' a : Tm 0}
    (hA : TyEq Γ A A') (ha : HasTy Γ A a)
    : HasTy Γ A' a
  | transfer {Γ : Ctx} {A B a : Tm 0}
    (hA : HasTy Γ A a) (hB : JEq Γ B a a)
    : HasTy Γ B a

theorem Ctx.HasTy.cast' {Γ ℓ A A' a} (hA : JEq Γ (.univ ℓ) A A') (ha : HasTy Γ A a)
  : HasTy Γ A' a := .cast hA.ty_eq ha

theorem Ctx.HasTy.ok {Γ A a} (h : HasTy Γ A a) : Ok Γ := by induction h <;> assumption

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
