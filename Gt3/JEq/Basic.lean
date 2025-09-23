import Gt3.Ctx
import Gt3.Syntax.Logic

inductive Ctx.JEq : Ctx → Tm 0 → Tm 0 → Tm 0 → Prop
  -- Congruence rules
  | fv' {Γ} {x : String} {A : Tm 0}
    (hΓ : JEq Γ .unit .null .null)
    (hx : Ctx.Lookup Γ x A)
    : JEq Γ A (Tm.fv x) (Tm.fv x)
  | univ' {Γ} {ℓ}
    : JEq Γ .unit .null .null → JEq Γ (.univ (ℓ + 1)) (.univ ℓ) (.univ ℓ)
  | empty' {Γ} {ℓ} : JEq Γ .unit .null .null → JEq Γ (.univ ℓ) .empty .empty
  | unit' {Γ} {ℓ} : JEq Γ .unit .null .null → JEq Γ (.univ ℓ) .unit .unit
  | eqn {Γ} {A a a' b b' : Tm 0} {ℓ : ULevel}
    (ha : JEq Γ A a a')
    (hb : JEq Γ A b b')
    : JEq Γ (.univ ℓ) (.eqn a b) (.eqn a' b')
  | pi {Γ} {A A' : Tm 0} {B B' : Tm 1} {ℓ : ULevel} {L : Finset String}
    (hA : JEq Γ (.univ ℓ) A A')
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ ℓ) (B.open x) (B'.open x))
    : JEq Γ (.univ ℓ) (.pi A B) (.pi A' B')
  | abs' {Γ} {A A' : Tm 0} {B b b' : Tm 1} {m n : ULevel} {L : Finset String}
    (hA : JEq Γ (.univ m) A A')
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hb : ∀ x ∉ L, JEq (Γ.cons x A) (B.open x) (b.open x) (b'.open x))
    : JEq Γ (A.pi B) (A.abs b) (A'.abs b')
  | app' {Γ} {A : Tm 0} {B : Tm 1} {f f' a a' Ba : Tm 0} {m n : ULevel} {L : Finset String}
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hA : JEq Γ (.univ m) A A)
    (hf : JEq Γ (A.pi B) f f')
    (ha : JEq Γ A a a')
    (hBa : JEq Γ (.univ n) (B.lst a) Ba)
    : JEq Γ Ba (f.app a) (f'.app a')
  | sigma {Γ} {A A' : Tm 0} {B B' : Tm 1} {ℓ : ULevel} {L : Finset String}
    (hA : JEq Γ (.univ ℓ) A A')
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ ℓ) (B.open x) (B'.open x))
    : JEq Γ (.univ ℓ) (.sigma A B) (.sigma A' B')
  | pair' {Γ} {A A' a a' b b' : Tm 0} {B B' : Tm 1} {m n : ULevel} {L : Finset String}
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    (hA : JEq Γ (.univ m) A A')
    (ha : JEq Γ A a a')
    (hb : JEq Γ (B.lst a) b b')
    : JEq Γ (.sigma A B) (.pair a b) (.pair a' b')
  | fst' {Γ} {A : Tm 0} {B : Tm 1} {p p' : Tm 0} {m n : ULevel} {L : Finset String}
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hA : JEq Γ (.univ m) A A)
    (hp : JEq Γ (.sigma A B) p p')
    : JEq Γ A (.fst p) (.fst p')
  | snd' {Γ}  {A : Tm 0} {B : Tm 1} {p p' Ba : Tm 0} {m n : ULevel} {L : Finset String}
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hA : JEq Γ (.univ m) A A)
    (hp : JEq Γ (.sigma A B) p p')
    (hBa : JEq Γ (.univ n) (B.lst (.fst p)) Ba)
    : JEq Γ Ba (.snd p) (.snd p')
  | dite' {Γ} {φ φ' A : Tm 0} {l l' r r' : Tm 1} {ℓ : ULevel} {L : Finset String}
    (hφ : JEq Γ (.univ 0) φ φ')
    (hA : JEq Γ (.univ ℓ) A A)
    (hl : ∀ x ∉ L, JEq (Γ.cons x φ) A (l.open x) (l'.open x))
    (hr : ∀ x ∉ L, JEq (Γ.cons x φ.not) A (r.open x) (r'.open x))
    : JEq Γ A (.dite φ l r) (.dite φ' l' r')
  | trunc {Γ} {A A' : Tm 0} {ℓ : ULevel}
    (hA : JEq Γ (.univ ℓ) A A')
    : JEq Γ (.univ 0) (.trunc A) (.trunc A')
  | choose' {Γ} {A A' : Tm 0} {φ φ' : Tm 1} {ℓ : ULevel} {L : Finset String}
    (hA : JEq Γ (.univ ℓ) A A')
    (hAI : JEq Γ (.univ 0) (.trunc A) .unit)
    (hφ : ∀x ∉ L, JEq (Γ.cons x A) (.univ 0) (φ.open x) (φ'.open x))
    : JEq Γ A (.choose A φ) (.choose A' φ')
  | nats' {Γ} : JEq Γ .unit .null .null → JEq Γ (.univ 1) .nats .nats
  | zero' {Γ} : JEq Γ .unit .null .null → JEq Γ .nats .zero .zero
  | succ {Γ n n'} : JEq Γ .nats n n' → JEq Γ .nats (.succ n) (.succ n')
  | natrec' {Γ ℓ C C' s s' z z' n n' ℓ' Cn} {L : Finset String}
    (hC : ∀x ∉ L, JEq (Γ.cons x .nats) (.univ ℓ) (C.open x) (C'.open x))
    (hs : ∀x ∉ L, JEq (Γ.cons x .nats) ((Tm.succArrow C).open x) (s.open x) (s'.open x))
    (hz : JEq Γ (C.lst .zero) z z')
    (hn : JEq Γ .nats n n')
    (hCn : JEq Γ (.univ ℓ') (C.lst n) Cn)
    : JEq Γ Cn (.natrec C s z n) (.natrec C' s' z' n')
  -- Meta
  | m_has_ty' {Γ} {A A' a a' : Tm 0} {ℓ}
    (hA : JEq Γ (.univ ℓ) A A')
    (ha : JEq Γ A a a')
    : JEq Γ .unit (.has_ty A a) (.has_ty A' a')
  -- Context well-formedness
  | nil_ok : JEq .nil .unit .null .null
  | cons_ok {Γ} {x : String} {A : Tm 0} {ℓ}
    (hΓ : JEq Γ .unit .null .null)
    (hx : x ∉ Γ.dv)
    (hA : JEq Γ (.univ ℓ) A A)
    : JEq (Γ.cons x A) .unit .null .null
  -- Propositions
  | trunc_inhab' {Γ} {A a : Tm 0}
    (ha : JEq Γ A a a)
    (lhs_wf : JEq Γ (.univ 0) (.trunc A) (.trunc A))
    (rhs_wf : JEq Γ (.univ 0) .unit .unit)
    : JEq Γ (.univ 0) (.trunc A) .unit
  -- Reduction
  | beta_app' {Γ} {A : Tm 0} {B b : Tm 1} {a ba Ba : Tm 0}
    (hf : JEq Γ (A.pi B) (A.abs b) (A.abs b))
    (ha : JEq Γ A a a)
    (lhs_wf : JEq Γ Ba (.app (A.abs b) a) (.app (A.abs b) a))
    (rhs_wf : JEq Γ Ba ba ba)
    (hba : JEq Γ Ba (b.lst a) ba)
    : JEq Γ Ba (.app (A.abs b) a) ba
  | beta_fst' {Γ}  {A : Tm 0} {B : Tm 1} {a b : Tm 0} {m n} {L : Finset String}
    (hA : JEq Γ (.univ m) A A)
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEq Γ (.sigma A B) (.pair a b) (.pair a b))
    (lhs_wf : JEq Γ A (.fst (.pair a b)) (.fst (.pair a b)))
    (rhs_wf : JEq Γ A a a)
    : JEq Γ A (.fst (.pair a b)) a
  | beta_snd' {Γ}  {A : Tm 0} {B : Tm 1} {a b Ba : Tm 0} {m n} {L : Finset String}
    (hA : JEq Γ (.univ m) A A)
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEq Γ (.sigma A B) (.pair a b) (.pair a b))
    (lhs_wf : JEq Γ Ba (.snd (.pair a b)) (.snd (.pair a b)))
    (rhs_wf : JEq Γ Ba b b)
    : JEq Γ Ba (.snd (.pair a b)) b
  | beta_dite_tt' {Γ} {A : Tm 0} {l r : Tm 1} {lu} {ℓ : ULevel} {L : Finset String}
    (hA : JEq Γ (.univ ℓ) A A)
    (hl : ∀ x ∉ L, JEq (Γ.cons x .unit) A (l.open x) (l.open x))
    (lhs_wf : JEq Γ A (.dite Tm.unit l r) (.dite Tm.unit l r))
    (rhs_wf : JEq Γ A (l.lst .null) (l.lst .null))
    (hlu : JEq Γ A (l.lst .null) lu)
    : JEq Γ A (.dite Tm.unit l r) lu
  | beta_dite_ff' {Γ} {A : Tm 0} {l r : Tm 1} {ru} {ℓ : ULevel} {L : Finset String}
    (hA : JEq Γ (.univ ℓ) A A)
    (hl : ∀ x ∉ L, JEq (Γ.cons x Tm.empty.not) A (r.open x) (r.open x))
    (lhs_wf : JEq Γ A (.dite Tm.empty l r) (.dite Tm.empty l r))
    (rhs_wf : JEq Γ A (r.lst .null) (r.lst .null))
    (hlu : JEq Γ A (r.lst .null) ru)
    : JEq Γ A (.dite Tm.empty l r) ru
  | beta_natrec_zero' {Γ ℓ C s z ℓ' Cz} {L : Finset String}
    (hC : ∀x ∉ L, JEq (Γ.cons x .nats) (.univ ℓ) (C.open x) (C.open x))
    (hs : ∀x ∉ L, JEq (Γ.cons x .nats) ((Tm.succArrow C).open x) (s.open x) (s.open x))
    (hz : JEq Γ (C.lst .zero) z z)
    (hCn : JEq Γ (.univ ℓ') (C.lst .zero) Cz)
    (lhs_wf : JEq Γ Cz (.natrec C s z .zero) (.natrec C s z .zero))
    (rhs_wf : JEq Γ Cz z z)
    : JEq Γ Cz (.natrec C s z .zero) z
  | beta_natrec_succ' {Γ ℓ C s z n ℓ' r Csn} {L : Finset String}
    (hC : ∀x ∉ L, JEq (Γ.cons x .nats) (.univ ℓ) (C.open x) (C.open x))
    (hs : ∀x ∉ L, JEq (Γ.cons x .nats) ((Tm.succArrow C).open x) (s.open x) (s.open x))
    (hz : JEq Γ (C.lst .zero) z z)
    (hn : JEq Γ .nats n n)
    (hCn : JEq Γ (.univ ℓ') (C.lst (.succ n)) Csn)
    (hr : JEq Γ Csn ((s.lst n).app (.natrec C s z n)) r)
    (lhs_wf : JEq Γ Csn (.natrec C s z (.succ n)) (.natrec C s z (.succ n)))
    (rhs_wf : JEq Γ Csn ((s.lst n).app (.natrec C s z n)) ((s.lst n).app (.natrec C s z n)))
    : JEq Γ Csn (.natrec C s z (.succ n)) ((s.lst n).app (.natrec C s z n))
  -- Specification
  | choose_spec' {Γ A φ φc ℓ} {L : Finset String}
    (hA : JEq Γ (.univ ℓ) A A)
    (hAI : JEq Γ (.univ 0) (.trunc A) .unit)
    (hφ : ∀x ∉ L, JEq (Γ.cons x A) (.univ 0) (φ.open x) (φ.open x))
    (hAφI : JEq Γ (.univ 0) (.exists A φ) .unit)
    (hφc : JEq Γ (.univ 0) (φ.lst (.choose A φ)) φc)
    (lhs_wf : JEq Γ (.univ 0) φc φc)
    (rhs_wf : JEq Γ (.univ 0) .unit .unit)
    : JEq Γ (.univ 0) φc .unit
  -- Reflexivity and extensionality
  | unit_ext {Γ} {a} : JEq Γ .unit a a → JEq Γ .unit a .null
  | prop_inhab_unit' {Γ} {A a} : JEq Γ (.univ 0) A A → JEq Γ A a a → JEq Γ (.univ 0) A .unit
  | pi_ext' {Γ} {A : Tm 0} {B : Tm 1} {f g : Tm 0} {m n} {L : Finset String}
    (hA : JEq Γ (.univ m) A A)
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : JEq Γ (A.pi B) f f)
    (hg : JEq Γ (A.pi B) g g)
    (hfg : ∀x ∉ L, JEq (Γ.cons x A) (B.open x) (f.app (.fv x)) (g.app (.fv x)))
    : JEq Γ (A.pi B) f g
  | sigma_ext' {Γ} {A : Tm 0} {B : Tm 1} {p q : Tm 0} {m n} {L : Finset String}
    (hA : JEq Γ (.univ m) A A)
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEq Γ (.sigma A B) p p)
    (hq : JEq Γ (.sigma A B) q q)
    (hpq1 : JEq Γ A (.fst p) (.fst q))
    (hpq2 : JEq Γ (B.lst (.fst p)) (.snd p) (.snd q))
    : JEq Γ (.sigma A B) p q
  | eqn_rfl {Γ} {A a b: Tm 0} : JEq Γ A a b → JEq Γ (.univ 0) (.eqn a b) .unit
  | eqn_ext {Γ} {A a b : Tm 0}
    : JEq Γ A a a → JEq Γ A b b → JEq Γ (.univ 0) (.eqn a b) .unit → JEq Γ A a b
  -- Symmetry and transitivity
  | symm {Γ} {A a b : Tm 0} : JEq Γ A a b → JEq Γ A b a
  | trans {Γ} {A a b c : Tm 0}
    (hab : JEq Γ A a b)
    (hbc : JEq Γ A b c)
    : JEq Γ A a c
  -- Casting
  | cast_level_le {Γ} {A A' : Tm 0} {lo hi : ULevel} (h : lo ≤ hi)
    (hA : JEq Γ (.univ lo) A A')
    : JEq Γ (.univ hi) A A'
  | cast' {Γ} {A A' a a' : Tm 0} {ℓ : ULevel}
    (hA : JEq Γ (.univ ℓ) A A')
    (ha : JEq Γ A a a')
    : JEq Γ A' a a'
  | transfer' {Γ} {A B a b : Tm 0}
    (hA : JEq Γ A a b) (ha : JEq Γ B a a)
    : JEq Γ B a b

theorem Ctx.JEq.pi' {Γ} {A A' : Tm 0} {B B' : Tm 1} {ℓ m n : ULevel} {L : Finset String}
  (hA : JEq Γ (.univ m) A A')
  (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
  (hm : m ≤ ℓ) (hn : n ≤ ℓ)
  : JEq Γ (.univ ℓ) (.pi A B) (.pi A' B')
  := .pi (hA.cast_level_le hm) (fun x hx => (hB x hx).cast_level_le hn)

theorem Ctx.JEq.sigma' {Γ} {A A' : Tm 0} {B B' : Tm 1} {ℓ m n : ULevel} {L : Finset String}
  (hA : JEq Γ (.univ m) A A')
  (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
  (hm : m ≤ ℓ) (hn : n ≤ ℓ)
  : JEq Γ (.univ ℓ) (.sigma A B) (.sigma A' B')
  := .sigma (hA.cast_level_le hm) (fun x hx => (hB x hx).cast_level_le hn)

def Ctx.WfEq (Γ : Ctx) (a b : Tm 0) : Prop := ∃A, JEq Γ A a b

theorem Ctx.WfEq.symm {Γ a b} (h : WfEq Γ a b) : WfEq Γ b a :=
  have ⟨A, h⟩ := h; ⟨A, h.symm⟩

def Ctx.IsWf (Γ : Ctx) (a : Tm 0) : Prop := WfEq Γ a a

theorem Ctx.WfEq.lhs {Γ a b} (h : WfEq Γ a b) : IsWf Γ a :=
  have ⟨A, h⟩ := h; ⟨A, h.trans h.symm⟩

theorem Ctx.WfEq.rhs {Γ a b} (h : WfEq Γ a b) : IsWf Γ b := h.symm.lhs

def Ctx.TyEq (Γ : Ctx) (A B : Tm 0) : Prop := ∃ℓ, JEq Γ (.univ ℓ) A B

theorem Ctx.JEq.cast {Γ A B} (h : TyEq Γ A B) {a b} (hab : JEq Γ A a b)
  : JEq Γ B a b := have ⟨_, h⟩ := h; h.cast' hab

theorem Ctx.TyEq.symm {Γ A B} (h : TyEq Γ A B) : TyEq Γ B A :=
  have ⟨ℓ, h⟩ := h; ⟨ℓ, h.symm⟩

theorem Ctx.JEq.cast_level {ℓ : ULevel} {Γ A B}
  (hAB : JEq Γ (.univ ℓ) A B) : JEq Γ (.univ (ℓ + 1)) A B := hAB.cast_level_le (by simp)

theorem Ctx.TyEq.trans {Γ A B C} (hAB : TyEq Γ A B) (hBC : TyEq Γ B C) : TyEq Γ A C :=
  have ⟨n, hAB⟩ := hAB; have ⟨m, hBC⟩ := hBC;
  ⟨n ⊔ m, (hAB.cast_level_le (by simp)).trans (hBC.cast_level_le (by simp))⟩

def Ctx.IsTy (Γ : Ctx) (A : Tm 0) : Prop := TyEq Γ A A

@[simp]
theorem Ctx.TyEq.refl_iff {Γ A} : TyEq Γ A A ↔ IsTy Γ A := Iff.rfl

theorem Ctx.TyEq.wf {Γ A B} (h : TyEq Γ A B) : WfEq Γ A B := have ⟨_, h⟩ := h; ⟨_, h⟩

theorem Ctx.IsTy.wf {Γ A} (h : Ctx.IsTy Γ A) : Ctx.IsWf Γ A := TyEq.wf h

theorem Ctx.TyEq.lhs {Γ A B} (h : TyEq Γ A B) : IsTy Γ A := h.trans h.symm

theorem Ctx.TyEq.rhs {Γ A B} (h : TyEq Γ A B) : IsTy Γ B := h.symm.lhs

def Ctx.IsInhab (Γ : Ctx) (A : Tm 0) : Prop := TyEq Γ (.trunc A) .unit

theorem Ctx.JEq.inhab_def {Γ ℓ A} (h : JEq Γ (.univ ℓ) (.trunc A) .unit)
  : IsInhab Γ A := ⟨ℓ, h⟩

theorem Ctx.TyEq.trunc {Γ A B} (h : TyEq Γ A B) : TyEq Γ (.trunc A) (.trunc B)
  := have ⟨_, h⟩ := h; ⟨0, h.trunc⟩

theorem Ctx.IsInhab.cast {Γ A B} (hAB : TyEq Γ A B) (hA : IsInhab Γ A)
  : IsInhab Γ B := hAB.symm.trunc.trans hA

def Ctx.IsUniv (Γ : Ctx) (A : Tm 0) : Prop := ∃ℓ, TyEq Γ A (.univ ℓ)

theorem Ctx.IsUniv.cast {Γ A B} (hAB : TyEq Γ A B) (hB : IsUniv Γ B)
  : IsUniv Γ A := have ⟨ℓ, hB⟩ := hB; ⟨ℓ, hAB.trans hB⟩

theorem Ctx.IsUniv.eq_iff {Γ A B} (hAB : TyEq Γ A B) : IsUniv Γ A ↔ IsUniv Γ B
  := ⟨.cast hAB.symm, .cast hAB⟩

def Ctx.HasTy' (Γ : Ctx) (A : Tm 0) (a : Tm 0) : Prop := JEq Γ A a a

theorem Ctx.JEq.lhs_ty' {Γ A a b} (h : JEq Γ A a b) : HasTy' Γ A a := h.trans h.symm

theorem Ctx.JEq.rhs_ty' {Γ A a b} (h : JEq Γ A a b) : HasTy' Γ A b := h.symm.lhs_ty'

theorem Ctx.JEq.ty_eq {Γ ℓ A B} (h : JEq Γ (.univ ℓ) A B) : TyEq Γ A B := ⟨ℓ, h⟩

theorem Ctx.JEq.lhs_is_ty {Γ ℓ A B} (h : JEq Γ (.univ ℓ) A B) : IsTy Γ A := h.lhs_ty'.ty_eq

theorem Ctx.JEq.rhs_is_ty {Γ ℓ A B} (h : JEq Γ (.univ ℓ) A B) : IsTy Γ B := h.rhs_ty'.ty_eq

theorem Ctx.JEq.wf_eq {Γ A a b} (h : JEq Γ A a b) : WfEq Γ a b := ⟨A, h⟩

theorem Ctx.HasTy'.is_wf {Γ A a} (h : HasTy' Γ A a) : IsWf Γ a := ⟨A, h⟩

theorem Ctx.JEq.lhs_is_wf {Γ A a b} (h : JEq Γ A a b) : IsWf Γ a := h.lhs_ty'.is_wf

theorem Ctx.JEq.rhs_is_wf {Γ A a b} (h : JEq Γ A a b) : IsWf Γ b := h.rhs_ty'.is_wf

theorem Ctx.WfEq.trans {Γ a b c} (hab : WfEq Γ a b) (hbc : WfEq Γ b c) : WfEq Γ a c :=
  have ⟨_, hab⟩ := hab;
  have ⟨_, hbc⟩ := hbc;
  ⟨_, hab.trans (hbc.transfer' hab.rhs_ty')⟩

theorem Ctx.WfEq.transfer' {Γ A a b} (hab : WfEq Γ a b) (hbc : HasTy' Γ A a) : JEq Γ A a b :=
  have ⟨_, hab⟩ := hab; hab.transfer' hbc

theorem Ctx.HasTy'.has_ty_univ {Γ U A} (h : HasTy' Γ U A) (hU : IsUniv Γ U) : IsTy Γ A
  := have ⟨ℓ, hU⟩ := hU; ⟨ℓ, h.cast hU⟩

inductive Ctx.Ok : Ctx → Prop
  | nil : Ok .nil
  | cons {Γ} {x : String} {A : Tm 0}
  (hΓ : Ok Γ) (hx : x ∉ Γ.dv) (hA : IsTy Γ A)
  : Ok (Γ.cons x A)

attribute [simp] Ctx.Ok.nil

theorem Ctx.JEq.ok {Γ A a b} (h : JEq Γ A a b) : Ok Γ := by
  induction h <;> repeat first | assumption | constructor

theorem Ctx.TyEq.ok {Γ A B} (h : TyEq Γ A B) : Ok Γ := have ⟨_, h⟩ := h; h.ok

theorem Ctx.IsTy.ok {Γ A} (h : IsTy Γ A) : Ok Γ := TyEq.ok h

theorem Ctx.WfEq.ok {Γ a b} (h : WfEq Γ a b) : Ok Γ := have ⟨_, h⟩ := h; h.ok

theorem Ctx.IsWf.ok {Γ a} (h : IsWf Γ a) : Ok Γ := WfEq.ok h

theorem Ctx.IsUniv.ok {Γ U} (h : IsUniv Γ U) : Ok Γ := have ⟨_, h⟩ := h; h.ok

theorem Ctx.IsInhab.ok {Γ A} (h : IsInhab Γ A) : Ok Γ := have ⟨_, h⟩ := h; h.ok

theorem Ctx.Ok.no_dup {Γ} (h : Ok Γ) : NoDup Γ := by induction h <;> constructor <;> assumption

theorem Ctx.Ok.head {Γ x A} (h : Ok (Ctx.cons Γ x A)) : x ∉ Γ.dv ∧ IsTy Γ A
  := by cases h; simp only [not_false_eq_true, and_self, *]

theorem Ctx.Ok.var {Γ x A} (h : Ok (Ctx.cons Γ x A)) : x ∉ Γ.dv
  := h.head.left

theorem Ctx.Ok.ty {Γ x A} (h : Ok (Ctx.cons Γ x A)) : IsTy Γ A
  := h.head.right

theorem Ctx.Ok.tail {Γ x A} (h : Ok (Ctx.cons Γ x A)) : Ok Γ
  := by cases h; assumption

theorem Ctx.Ok.cons_iff {Γ x A} : Ok (Ctx.cons Γ x A) ↔ Ok Γ ∧ x ∉ Γ.dv ∧ IsTy Γ A
  := ⟨fun h => ⟨h.tail, h.head⟩, fun ⟨hΓ, hx, hA⟩ => hΓ.cons hx hA⟩

theorem Ctx.JEq.null {Γ} (h : Ok Γ) : JEq Γ .unit .null .null := by
  induction h with
  | nil => exact .nil_ok
  | cons _ _ hA => cases hA; constructor <;> assumption

theorem Ctx.JEq.fv {Γ x A} (h : Ok Γ) (hx : Ctx.Lookup Γ x A) : JEq Γ A (.fv x) (.fv x)
  := .fv' (.null h) hx

theorem Ctx.JEq.unit {Γ} {ℓ} (h : Ok Γ) : JEq Γ (.univ ℓ) .unit .unit := .unit' (.null h)

theorem Ctx.JEq.empty {Γ} {ℓ} (h : Ok Γ) : JEq Γ (.univ ℓ) .empty .empty := .empty' (.null h)

theorem Ctx.JEq.univ {Γ} {ℓ} (h : Ok Γ) : JEq Γ (.univ (ℓ + 1)) (.univ ℓ) (.univ ℓ)
  := .univ' (.null h)

theorem Ctx.JEq.not {Γ φ φ'} (hφ : JEq Γ (.univ 0) φ φ')
  : JEq Γ (.univ 0) (φ.not) (φ'.not) := .eqn hφ (.empty hφ.ok)

theorem Ctx.JEq.nats {Γ} (h : Ok Γ) : JEq Γ (.univ 1) .nats .nats
  := .nats' (.null h)

theorem Ctx.JEq.zero {Γ} (h : Ok Γ) : JEq Γ .nats .zero .zero
  := .zero' (.null h)

theorem Ctx.IsTy.top_cf {Γ A} {B : Tm 1} {L : Finset String}
  (hB : ∀ x ∉ L, IsTy (Γ.cons x A) (B.open x)) : IsTy Γ A
  := have ⟨x, hx⟩ := L.exists_notMem; (hB x hx).ok.ty

theorem Ctx.JEq.app_f
  {Γ} {A : Tm 0} {B : Tm 1} {f a f' a' Ba : Tm 0} {m n : ULevel} {L : Finset String}
  (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
  (hA : JEq Γ (.univ m) A A)
  (hf : JEq Γ (A.pi B) f f') (ha : JEq Γ A a a') (hBa : TyEq Γ (B.lst a) Ba)
  : JEq Γ Ba (f.app a) (f'.app a') :=
  have ⟨ℓ, hBa⟩ := hBa;
  .app' (n := n ⊔ ℓ)
        (fun x hx => (hB x hx).cast_level_le (by simp)) hA hf ha
        (hBa.cast_level_le (by simp))

theorem Ctx.JEq.snd_f {Γ} {A : Tm 0} {B : Tm 1} {p p' Ba : Tm 0} {m n : ULevel} {L : Finset String}
  (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
  (hA : JEq Γ (.univ m) A A)
  (hp : JEq Γ (A.sigma B) p p') (hBa : TyEq Γ (B.lst p.fst) Ba)
  : JEq Γ Ba (.snd p) (.snd p') :=
  have ⟨ℓ, hBa⟩ := hBa;
  .snd' (n := n ⊔ ℓ)
        (fun x hx => (hB x hx).cast_level_le (by simp)) hA hp
        (hBa.cast_level_le (by simp))

theorem Ctx.JEq.choose {Γ} {A A' : Tm 0} {φ φ' : Tm 1} {ℓ : ULevel} {L : Finset String}
  (hA : JEq Γ (.univ ℓ) A A')
  (hAI : IsInhab Γ A)
  (hφ : ∀ x ∉ L, JEq (Γ.cons x A) (.univ 0) (φ.open x) (φ'.open x))
  : JEq Γ A (.choose A φ) (.choose A' φ') :=
  have ⟨_, hAI⟩ := hAI;  .choose' hA (hAI.transfer' (.trunc hA.lhs_ty')) hφ

theorem Ctx.JEq.natrec {Γ ℓ C C' s s' z z' n n' Cn} {L : Finset String}
  (hC : ∀ x ∉ L, JEq (Γ.cons x .nats) (.univ ℓ) (C.open x) (C'.open x))
    (hs : ∀ x ∉ L, JEq (Γ.cons x .nats) ((Tm.succArrow C).open x) (s.open x) (s'.open x))
    (hz : JEq Γ (C.lst .zero) z z')
    (hn : JEq Γ .nats n n')
    (hCn : TyEq Γ (C.lst n) Cn)
    : JEq Γ Cn (.natrec C s z n) (.natrec C' s' z' n')
  := have ⟨_, hCn⟩ := hCn; .natrec' hC hs hz hn hCn

theorem Ctx.JEq.ite' {Γ A φ φ' l l' r r' ℓ} {L : Finset String}
  (hφ : JEq Γ (.univ 0) φ φ')
  (hA : JEq Γ (.univ ℓ) A A)
  (hl : ∀ x ∉ L, JEq (Γ.cons x φ) A l l')
  (hr : ∀ x ∉ L, JEq (Γ.cons x φ.not) A r r')
  : JEq Γ A (.ite φ l r) (.ite φ' l' r')
  := .dite' hφ hA (fun x hx => (by convert hl x hx <;> simp))
                  (fun x hx => (by convert hr x hx <;> simp))

syntax "jeq_congr_f" : tactic

macro_rules
  | `(tactic| jeq_congr_f) => `(tactic| first
    | apply Ctx.JEq.fv
    | apply Ctx.JEq.univ
    | apply Ctx.JEq.empty
    | apply Ctx.JEq.unit
    | apply Ctx.JEq.null
    | apply Ctx.JEq.eqn
    | apply Ctx.JEq.pi
    | apply Ctx.JEq.abs'
    | apply Ctx.JEq.app_f
    | apply Ctx.JEq.sigma
    | apply Ctx.JEq.pair'
    | apply Ctx.JEq.fst'
    | apply Ctx.JEq.snd_f
    | apply Ctx.JEq.dite'
    | apply Ctx.JEq.trunc
    | apply Ctx.JEq.choose
    | apply Ctx.JEq.nats
    | apply Ctx.JEq.zero
    | apply Ctx.JEq.succ
    | apply Ctx.JEq.natrec
    | apply Ctx.JEq.m_has_ty'
  )

theorem Ctx.IsTy.univ {Γ ℓ} (h : Ok Γ) : IsTy Γ (.univ ℓ) := ⟨ℓ + 1, .univ h⟩

theorem Ctx.IsUniv.univ {Γ ℓ} (h : Ok Γ) : IsUniv Γ (.univ ℓ) := ⟨ℓ, IsTy.univ h⟩

theorem Ctx.IsUniv.is_ty {Γ U} (h : IsUniv Γ U) : IsTy Γ U := have ⟨_, h⟩ := h; h.lhs

@[simp] theorem Ctx.IsUniv.univ_iff {Γ ℓ} : IsUniv Γ (.univ ℓ) ↔ Ok Γ := ⟨IsUniv.ok, IsUniv.univ⟩

theorem Ctx.IsTy.empty {Γ} (h : Ok Γ) : IsTy Γ .empty := ⟨0, .empty h⟩

theorem Ctx.IsTy.unit {Γ} (h : Ok Γ) : IsTy Γ .unit := ⟨0, .unit h⟩

theorem Ctx.IsTy.nats {Γ} (h : Ok Γ) : IsTy Γ .nats := ⟨1, .nats h⟩

@[simp] theorem Ctx.IsTy.univ_iff {Γ ℓ} : IsTy Γ (.univ ℓ) ↔ Ok Γ := ⟨IsTy.ok, IsTy.univ⟩

@[simp] theorem Ctx.IsTy.empty_iff {Γ} : IsTy Γ .empty ↔ Ok Γ := ⟨IsTy.ok, IsTy.empty⟩

@[simp] theorem Ctx.IsTy.unit_iff {Γ} : IsTy Γ .unit ↔ Ok Γ := ⟨IsTy.ok, IsTy.unit⟩

@[simp] theorem Ctx.IsTy.nats_iff {Γ} : IsTy Γ .nats ↔ Ok Γ := ⟨IsTy.ok, IsTy.nats⟩

theorem Ctx.TyEq.not {Γ φ φ'} (h : JEq Γ (.univ 0) φ φ') : TyEq Γ (φ.not) (φ'.not) := h.not.ty_eq

theorem Ctx.IsTy.not {Γ φ φ'} (h : JEq Γ (.univ 0) φ φ') : IsTy Γ (φ.not) := h.not.lhs_is_ty

theorem Ctx.IsTy.not_rhs {Γ φ φ'} (h : JEq Γ (.univ 0) φ φ') : IsTy Γ (φ'.not) := h.not.rhs_is_ty

theorem Ctx.Ok.iff_null {Γ} : JEq Γ .unit .null .null ↔ Ok Γ := ⟨JEq.ok, JEq.null⟩

theorem Finset.cof_eq_or.{u} {α : Type u} [Infinite α] {L : Finset α} (x : α) (P : α → Prop)
  (h : ∀ y ∉ L, x = y ∨ P x) : P x := by
  open Classical in
  have ⟨y, hy⟩ := L.exists_notMem;
  have hy' := h y hy
  cases hy' with
  | inr hy' => exact hy'
  | inl hy' =>
  cases hy'
  have ⟨z, hz⟩ := (insert x L).exists_notMem
  simp at hz
  have hx := h z hz.right
  cases hx with
  | inr hx => exact hx
  | inl hx => cases hx; exact (hz.left rfl).elim

theorem Finset.cof_eq_or_iff.{u}
  {α : Type u} [Infinite α] {L : Finset α} (x : α) (P : α → Prop)
  : (∀ y ∉ L, x = y ∨ P x) ↔ P x := ⟨cof_eq_or x P, fun h => by simp [h]⟩

theorem Tm.scoped_of_cf {k} {L V : Finset String} {a : Tm (k + 1)}
  (h : ∀ x ∉ L, (a.open x).fvs ⊆ insert x V)
  : a.fvs ⊆ V := by induction a using succIndOn with
  | fv =>
    simp [Finset.cof_eq_or_iff] at h
    simp [h]
  | _ =>
    simp only [fvs, «open», Finset.union_subset_iff, forall_and] at h
    simp only [fvs, Finset.union_subset_iff, Finset.empty_subset]
    <;> (try constructorm* _ ∧ _)
    <;> (try casesm* _ ∧ _)
    <;> apply_assumption
    <;> assumption

theorem Tm.cf_scoped_iff {k} (L V : Finset String) (a : Tm (k + 1))
  : (∀ x ∉ L, (a.open x).fvs ⊆ insert x V) ↔ a.fvs ⊆ V
  := ⟨fun h => scoped_of_cf h,
      fun h x _ => Finset.Subset.trans (a.fvs_open x) (Finset.insert_subset_insert _ h)⟩

theorem Ctx.JEq.scoped_all {Γ A a b} (h : JEq Γ A a b)
  : Scoped Γ ∧ A.fvs ⊆ Γ.dv ∧ a.fvs ⊆ Γ.dv ∧ b.fvs ⊆ Γ.dv := by induction h with
  | _ =>
    (try simp only [forall_and, Ctx.dv, Tm.cf_scoped_iff, Tm.fvs, Finset.union_subset_iff] at *)
    simp [Scoped.cons_iff, *]
    <;> {
      constructor
      · apply Scoped.lookup
        · simp [*]
        · assumption
      · apply Lookup.dv; assumption
    }

theorem Ctx.JEq.ctx_scoped {Γ A a b} (h : JEq Γ A a b) : Scoped Γ := h.scoped_all.left

theorem Ctx.JEq.ty_scoped {Γ A a b} (h : JEq Γ A a b) : A.fvs ⊆ Γ.dv := h.scoped_all.right.left

theorem Ctx.JEq.lhs_scoped {Γ A a b} (h : JEq Γ A a b) : a.fvs ⊆ Γ.dv
  := h.scoped_all.right.right.left

theorem Ctx.JEq.rhs_scoped {Γ A a b} (h : JEq Γ A a b) : b.fvs ⊆ Γ.dv
  := h.scoped_all.right.right.right

theorem Ctx.IsTy.scoped {Γ A} (h : IsTy Γ A) : A.fvs ⊆ Γ.dv := have ⟨_, h⟩ := h; h.lhs_scoped

theorem Ctx.JEq.top_var {Γ : Ctx} {x A} (h : Ok (Γ.cons x A)) : JEq (Γ.cons x A) A (.fv x) (.fv x)
  := .fv h (.here _ _ _)

theorem Ctx.JEq.top_var_iff {Γ : Ctx} {x A}
  : JEq (Γ.cons x A) A (.fv x) (.fv x) ↔ Ok (Γ.cons x A)
  := ⟨JEq.ok, JEq.top_var⟩

theorem Ctx.JEq.cf_scoped {Γ : Ctx} {A : Tm 0} {B a b : String → Tm 0}
  {L : Finset String} (h : ∀ x ∉ L, JEq (Γ.cons x A) (B x) (a x) (b x))
  : Γ.dv ⊆ L := by
  intro x hx
  by_contra hx'
  exact (h x hx').ok.var hx

theorem Ctx.JEq.ty_scoped_cf {Γ : Ctx} {A : Tm 0} {B : Tm 1} {a b : String → Tm 0}
  {L : Finset String} (h : ∀ x ∉ L, JEq (Γ.cons x A) (B.open x) (a x) (b x))
  : B.fvs ⊆ Γ.dv := by
  intro y hy
  have ⟨x, hx⟩ := (insert y L).exists_notMem
  simp at hx
  have hB := ((h x hx.2).ty_scoped)
  have hxy := ((B.subset_fvs_open x).trans hB) hy
  simp at hxy
  cases hxy
  · exact (Ne.symm hx.1 ‹_›).elim
  · assumption

theorem Ctx.JEq.lhs_scoped_cf
  {Γ : Ctx} {A : Tm 0} {B : String → Tm 0} {a : Tm 1} {b : String → Tm 0}
  {L : Finset String} (h : ∀ x ∉ L, JEq (Γ.cons x A) (B x) (a.open x) (b x))
  : a.fvs ⊆ Γ.dv := by
  intro y hy
  have ⟨x, hx⟩ := (insert y L).exists_notMem
  simp at hx
  have ha := ((h x hx.2).lhs_scoped)
  have hxy := ((a.subset_fvs_open x).trans ha) hy
  simp at hxy
  cases hxy
  · exact (Ne.symm hx.1 ‹_›).elim
  · assumption

theorem Ctx.JEq.rhs_scoped_cf
  {Γ : Ctx} {A : Tm 0} {B : String → Tm 0} {a : String → Tm 0} {b : Tm 1}
  {L : Finset String} (h : ∀ x ∉ L, JEq (Γ.cons x A) (B x) (a x) (b.open x)) : b.fvs ⊆ Γ.dv
  := lhs_scoped_cf (fun x hx => (h x hx).symm)
