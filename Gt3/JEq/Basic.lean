import Gt3.Ctx

inductive Ctx.JEq : Ctx → Tm 0 → Tm 0 → Tm 0 → Prop
  -- Congruence rules
  | fv {Γ : Ctx} {x : String} {A : Tm 0}
  (hΓ : JEq Γ .unit .null .null)
  (hx : Ctx.Lookup Γ x A)
  : JEq Γ A (Tm.fv x) (Tm.fv x)
  | univ {Γ : Ctx} {ℓ ℓ'} (h : ℓ < ℓ')
  : JEq Γ .unit .null .null → JEq Γ (.univ ℓ') (.univ ℓ) (.univ ℓ)
  | empty {Γ : Ctx} {ℓ} : JEq Γ .unit .null .null → JEq Γ (.univ ℓ) .empty .empty
  | unit {Γ : Ctx} {ℓ} : JEq Γ .unit .null .null → JEq Γ (.univ ℓ) .unit .unit
  | eqn {Γ : Ctx} {A a a' b b' : Tm 0}
  (ha : JEq Γ A a a')
  (hb : JEq Γ A b b')
  : JEq Γ (.univ 0) (.eqn a b) (.eqn a' b')
  | pi {Γ : Ctx} {A A' : Tm 0} {B B' : Tm 1} {ℓ m n : ℕ} {L : Finset String}
  (hA : JEq Γ (.univ m) A A')
  (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
  (hm : m ≤ ℓ) (hn : n ≤ ℓ) (hℓ : 1 ≤ ℓ)
  : JEq Γ (.univ (max m n)) (.pi A B) (.pi A' B')
  | abs {Γ : Ctx} {A A' : Tm 0} {B B' b b' : Tm 1} {t t' : Tm 1} {m n : ℕ} {L : Finset String}
  (hA : JEq Γ (.univ m) A A')
  (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
  (hb : ∀ x ∉ L, JEq (Γ.cons x A) (B.open x) (b.open x) (b'.open x))
  : JEq Γ (A.pi B) (A.abs b) (A'.abs b')
  | app {Γ : Ctx} {A : Tm 0} {B : Tm 1} {f f' a a' Ba : Tm 0} {n : ℕ} {L : Finset String}
  (hf : JEq Γ (A.pi B) f f')
  (ha : JEq Γ A a a')
  (hBa : JEq Γ (.univ n) (B.lst a) Ba)
  : JEq Γ Ba (f.app a) (f'.app a')
  -- Context well-formedness
  | nil_ok : JEq .nil .unit .null .null
  | cons_ok {Γ : Ctx} {x : String} {A : Tm 0} {ℓ}
  (hΓ : JEq Γ .unit .null .null)
  (hx : x ∉ Γ.dv)
  (hA : JEq Γ (.univ ℓ) A A)
  : JEq (Γ.cons x A) .unit .null .null
  -- Reduction
  | beta_app {Γ : Ctx} {A : Tm 0} {B b : Tm 1} {a ba Ba : Tm 0} {n : ℕ} {L : Finset String}
  (hf : JEq Γ (A.pi B) (A.abs b) (A.abs b))
  (ha : JEq Γ A a a)
  (hba : JEq Γ Ba (b.lst a) ba)
  : JEq Γ Ba (.app (A.abs b) a) ba
  -- Reflexivity and extensionality
  | eqn_rfl {Γ : Ctx} {A a b: Tm 0} : JEq Γ A a b → JEq Γ (.univ 0) (.eqn a b) .unit
  | eqn_ext {Γ : Ctx} {A a b : Tm 0}
  : JEq Γ A a a → JEq Γ A b b → JEq Γ (.univ 0) (.eqn a b) .unit → JEq Γ A a b
  -- Symmetry and transitivity
  | symm {Γ : Ctx} {A a b : Tm 0} : JEq Γ A a b → JEq Γ A b a
  | trans {Γ : Ctx} {A a b c : Tm 0}
  (hab : JEq Γ A a b)
  (hbc : JEq Γ A b c)
  : JEq Γ A a c
  -- Casting
  | cast {Γ : Ctx} {A A' a a' : Tm 0} {ℓ : ℕ}
  (hA : JEq Γ (.univ ℓ) A A')
  (ha : JEq Γ A a a')
  : JEq Γ A' a a'

def Ctx.WfEq (Γ : Ctx) (a b : Tm 0) : Prop := ∃A, JEq Γ A a b

def Ctx.IsWf (Γ : Ctx) (a : Tm 0) : Prop := WfEq Γ a a

def Ctx.TyEq (Γ : Ctx) (A B : Tm 0) : Prop := ∃ℓ, JEq Γ (.univ ℓ) A B

def Ctx.IsTy (Γ : Ctx) (A : Tm 0) : Prop := TyEq Γ A A

theorem Ctx.TyEq.wf {Γ A B} (h : TyEq Γ A B) : WfEq Γ A B := have ⟨_, h⟩ := h; ⟨_, h⟩

theorem Ctx.IsTy.wf {Γ A} (h : Ctx.IsTy Γ A) : Ctx.IsWf Γ A := TyEq.wf h

def Ctx.HasTy' (Γ : Ctx) (A : Tm 0) (a : Tm 0) : Prop := JEq Γ A a a

theorem Ctx.JEq.lhs_ty' {Γ A a b} (h : JEq Γ A a b) : HasTy' Γ A a := h.trans h.symm

theorem Ctx.JEq.rhs_ty' {Γ A a b} (h : JEq Γ A a b) : HasTy' Γ A b := h.symm.lhs_ty'

def Ctx.Ok' (Γ : Ctx) : Prop := HasTy' Γ .unit .null

inductive Ctx.Ok : Ctx → Prop
  | nil : Ok .nil
  | cons {Γ : Ctx} {x : String} {A : Tm 0}
  (hΓ : Ok Γ) (hx : x ∉ Γ.dv) (hA : IsTy Γ A)
  : Ok (Γ.cons x A)
