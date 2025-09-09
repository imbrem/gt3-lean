import Gt3.Ctx

inductive Ctx.JEq : Ctx → Tm 0 → Tm 0 → Tm 0 → Prop
  -- Congruence rules
  | fv' {Γ : Ctx} {x : String} {A : Tm 0}
    (hΓ : JEq Γ .unit .null .null)
    (hx : Ctx.Lookup Γ x A)
    : JEq Γ A (Tm.fv x) (Tm.fv x)
  | univ' {Γ : Ctx} {ℓ}
    : JEq Γ .unit .null .null → JEq Γ (.univ (ℓ + 1)) (.univ ℓ) (.univ ℓ)
  | empty' {Γ : Ctx} {ℓ} : JEq Γ .unit .null .null → JEq Γ (.univ ℓ) .empty .empty
  | unit' {Γ : Ctx} {ℓ} : JEq Γ .unit .null .null → JEq Γ (.univ ℓ) .unit .unit
  | eqn {Γ : Ctx} {A a a' b b' : Tm 0} {ℓ : ℕ}
    (ha : JEq Γ A a a')
    (hb : JEq Γ A b b')
    : JEq Γ (.univ ℓ) (.eqn a b) (.eqn a' b')
  | pi {Γ : Ctx} {A A' : Tm 0} {B B' : Tm 1} {ℓ m n : ℕ} {L : Finset String}
    (hA : JEq Γ (.univ m) A A')
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    (hm : m ≤ ℓ) (hn : n ≤ ℓ) (hℓ : 1 ≤ ℓ)
    : JEq Γ (.univ ℓ) (.pi A B) (.pi A' B')
  | abs {Γ : Ctx} {A A' : Tm 0} {B b b' : Tm 1} {m : ℕ} {L : Finset String}
    (hA : JEq Γ (.univ m) A A')
    (hb : ∀ x ∉ L, JEq (Γ.cons x A) (B.open x) (b.open x) (b'.open x))
    : JEq Γ (A.pi B) (A.abs b) (A'.abs b')
  | app' {Γ : Ctx} {A : Tm 0} {B : Tm 1} {f f' a a' Ba : Tm 0} {n : ℕ}
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
  | beta_app {Γ : Ctx} {A : Tm 0} {B b : Tm 1} {a ba Ba : Tm 0}
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
  | cast_level {Γ : Ctx} {A A' : Tm 0} {ℓ : ℕ}
    (hA : JEq Γ (.univ ℓ) A A')
    : JEq Γ (.univ (ℓ + 1)) A A'
  | cast' {Γ : Ctx} {A A' a a' : Tm 0} {ℓ : ℕ}
    (hA : JEq Γ (.univ ℓ) A A')
    (ha : JEq Γ A a a')
    : JEq Γ A' a a'

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

theorem Ctx.JEq.cast_level_le {ℓ ℓ' : ℕ} (hℓ : ℓ ≤ ℓ') {Γ A B}
  (hAB : JEq Γ (.univ ℓ) A B) : JEq Γ (.univ ℓ') A B := by
  induction hℓ with
  | refl => assumption
  | step => apply cast_level; assumption

theorem Ctx.TyEq.trans {Γ A B C} (hAB : TyEq Γ A B) (hBC : TyEq Γ B C) : TyEq Γ A C :=
  have ⟨n, hAB⟩ := hAB; have ⟨m, hBC⟩ := hBC;
  ⟨n ⊔ m, (hAB.cast_level_le (by simp)).trans (hBC.cast_level_le (by simp))⟩

def Ctx.IsTy (Γ : Ctx) (A : Tm 0) : Prop := TyEq Γ A A

theorem Ctx.TyEq.wf {Γ A B} (h : TyEq Γ A B) : WfEq Γ A B := have ⟨_, h⟩ := h; ⟨_, h⟩

theorem Ctx.IsTy.wf {Γ A} (h : Ctx.IsTy Γ A) : Ctx.IsWf Γ A := TyEq.wf h

theorem Ctx.TyEq.lhs {Γ A B} (h : TyEq Γ A B) : IsTy Γ A := h.trans h.symm

theorem Ctx.TyEq.rhs {Γ A B} (h : TyEq Γ A B) : IsTy Γ B := h.symm.lhs

def Ctx.IsUniv (Γ : Ctx) (A : Tm 0) : Prop := ∃ℓ, TyEq Γ A (.univ ℓ)

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

theorem Ctx.HasTy'.has_ty_univ {Γ U A} (h : HasTy' Γ U A) (hU : IsUniv Γ U) : IsTy Γ A
  := have ⟨ℓ, hU⟩ := hU; ⟨ℓ, h.cast hU⟩

inductive Ctx.Ok : Ctx → Prop
  | nil : Ok .nil
  | cons {Γ : Ctx} {x : String} {A : Tm 0}
  (hΓ : Ok Γ) (hx : x ∉ Γ.dv) (hA : IsTy Γ A)
  : Ok (Γ.cons x A)

attribute [simp] Ctx.Ok.nil

theorem Ctx.JEq.ok {Γ A a b} (h : JEq Γ A a b) : Ok Γ := by
  induction h <;> repeat first | assumption | constructor

theorem Ctx.TyEq.ok {Γ A B} (h : TyEq Γ A B) : Ok Γ := have ⟨_, h⟩ := h; h.ok

theorem Ctx.IsTy.ok {Γ A} (h : IsTy Γ A) : Ok Γ := TyEq.ok h

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

theorem Ctx.JEq.app {Γ} {A : Tm 0} {B : Tm 1} {f a f' a' Ba : Tm 0}
  (hf : JEq Γ (A.pi B) f f') (ha : JEq Γ A a a') (hBa : TyEq Γ (B.lst a) Ba)
  : JEq Γ Ba (f.app a) (f'.app a') := have ⟨_, hBa⟩ := hBa; .app' hf ha hBa

syntax "jeq_congr" : tactic

macro_rules
  | `(tactic| jeq_congr) => `(tactic| first
    | apply Ctx.JEq.fv
    | apply Ctx.JEq.univ
    | apply Ctx.JEq.empty
    | apply Ctx.JEq.unit
    | apply Ctx.JEq.null
    | apply Ctx.JEq.eqn
    | apply Ctx.JEq.pi
    | apply Ctx.JEq.abs
    | apply Ctx.JEq.app
  )

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
