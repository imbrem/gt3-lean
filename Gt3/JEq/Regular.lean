import Gt3.JEq.Subst

theorem Ctx.JEq.to_cf {Γ : Ctx} {x} {A} {B a b : Tm 1}
  (h : JEq (Γ.cons x A) (B.open x) (a.open x) (b.open x))
  (hB : x ∉ B.fvs) (ha : x ∉ a.fvs) (hb : x ∉ b.fvs)
  : ∀ y ∉ Γ.dv , JEq (Γ.cons y A) (B.open y) (a.open y) (b.open y) := by
  intro y hy
  convert h.ls1' (SEq.rename_top hy h.ok.var h.ok.ty)
  <;> rw [Tm.ls_lset, Tm.lsv_open (hx := ‹_›), Tm.lst_of_fv]

theorem Ctx.JEq.to_cf_univ {Γ : Ctx} {x} {A ℓ} {a b : Tm 1}
  (h : JEq (Γ.cons x A) (.univ ℓ) (a.open x) (b.open x))
  (ha : x ∉ a.fvs) (hb : x ∉ b.fvs)
  : ∀ y ∉ Γ.dv, JEq (Γ.cons y A) (.univ ℓ) (a.open y) (b.open y)
  := by
  intro y hy
  rw [<-Tm.open_univ (x := x)] at h
  rw [<-Tm.open_univ (x := y)]
  apply h.to_cf <;> simp [*]

def Ctx.JEq.fvs {Γ A a b} (_ : JEq Γ A a b) : Finset String := A.fvs ∪ a.fvs ∪ b.fvs

theorem Ctx.JEq.to_cf_u {Γ : Ctx} {x} {A} {B a b : Tm 1}
  (h : JEq (Γ.cons x A) (B.open x) (a.open x) (b.open x))
  (hx : x ∉ B.fvs ∪ a.fvs ∪ b.fvs)
  : ∀ y ∉ Γ.dv , JEq (Γ.cons y A) (B.open y) (a.open y) (b.open y) := by
  simp only [Finset.notMem_union] at hx; apply h.to_cf <;> simp [*]

theorem Ctx.TyEq.max_univ_dv' {Γ : Ctx} {A} {B B' : Tm 1} {L : Finset String}
  (hB : ∀ x ∉ L, TyEq (Γ.cons x A) (B.open x) (B'.open x))
  : ∃ℓ, ∀ x ∉ Γ.dv, JEq (Γ.cons x A) (.univ ℓ) (B.open x) (B'.open x)
  := by
  have ⟨x, hx⟩ := (L ∪ B.fvs ∪ B'.fvs).exists_notMem;
  simp only [Finset.notMem_union] at hx
  have ⟨n, hB⟩ := hB x hx.left.left;
  exact ⟨n, hB.to_cf_univ hx.left.right hx.right⟩

theorem Ctx.TyEq.max_univ' {Γ : Ctx} {A} {B B' : Tm 1} {L : Finset String}
  (hB : ∀ x ∉ L, TyEq (Γ.cons x A) (B.open x) (B'.open x))
  : ∃ℓ, ∀ x ∉ L, JEq (Γ.cons x A) (.univ ℓ) (B.open x) (B'.open x)
  := have ⟨ℓ, h⟩ := max_univ_dv' hB; ⟨ℓ, fun x hx => h _ fun hx' => (hB x hx).ok.var hx'⟩

theorem Ctx.TyEq.max_univ_iff' {Γ : Ctx} {A} {B B' : Tm 1} {L : Finset String}
  : (∀ x ∉ L, TyEq (Γ.cons x A) (B.open x) (B'.open x))
  ↔ ∃ℓ, ∀ x ∉ L, JEq (Γ.cons x A) (.univ ℓ) (B.open x) (B'.open x)
  := ⟨max_univ', fun ⟨ℓ, h⟩ x hx => ⟨ℓ, h x hx⟩⟩

theorem Ctx.TyEq.pi {Γ A A' B B'} {L : Finset String}
  (hA : TyEq Γ A A') (hB : ∀ x ∉ L, TyEq (Γ.cons x A) (B.open x) (B'.open x))
  : TyEq Γ (.pi A B) (.pi A' B')
  := by
  have ⟨m, hA⟩ := hA;
  have ⟨n, hB⟩ := TyEq.max_univ' hB;
  exists m ⊔ n ⊔ 1
  apply JEq.pi hA hB <;> simp

theorem Ctx.TyEq.sigma {Γ A A' B B'} {L : Finset String}
  (hA : TyEq Γ A A') (hB : ∀ x ∉ L, TyEq (Γ.cons x A) (B.open x) (B'.open x))
  : TyEq Γ (.sigma A B) (.sigma A' B')
  := by
  have ⟨m, hA⟩ := hA;
  have ⟨n, hB⟩ := TyEq.max_univ' hB;
  exists m ⊔ n ⊔ 1
  apply JEq.sigma hA hB <;> simp

theorem Ctx.IsTy.max_univ_dv' {Γ : Ctx} {A} {B : Tm 1} {L : Finset String}
  (hB : ∀ x ∉ L, IsTy (Γ.cons x A) (B.open x))
  : ∃ℓ, ∀ x ∉ Γ.dv, HasTy' (Γ.cons x A) (.univ ℓ) (B.open x)
  := TyEq.max_univ_dv' hB

theorem Ctx.IsTy.max_univ' {Γ : Ctx} {A} {B : Tm 1} {L : Finset String}
  (hB : ∀ x ∉ L, IsTy (Γ.cons x A) (B.open x))
  : ∃ℓ, ∀ x ∉ L, HasTy' (Γ.cons x A) (.univ ℓ) (B.open x)
  := TyEq.max_univ' hB

theorem Ctx.IsTy.max_univ_iff' {Γ : Ctx} {A} {B : Tm 1} {L : Finset String}
  : (∀ x ∉ L, IsTy (Γ.cons x A) (B.open x)) ↔ ∃ℓ, ∀ x ∉ L, HasTy' (Γ.cons x A) (.univ ℓ) (B.open x)
  := ⟨max_univ', fun ⟨ℓ, h⟩ x hx => ⟨ℓ, h x hx⟩⟩

theorem Ctx.IsTy.pi {Γ A B} {L : Finset String}
  (hB : ∀ x ∉ L, IsTy (Γ.cons x A) (B.open x)) : IsTy Γ (.pi A B)
  := have ⟨x, hx⟩ := L.exists_notMem; TyEq.pi (hB x hx).ok.ty hB

theorem Ctx.IsTy.sigma {Γ A B} {L : Finset String}
  (hB : ∀ x ∉ L, IsTy (Γ.cons x A) (B.open x)) : IsTy Γ (.sigma A B)
  := have ⟨x, hx⟩ := L.exists_notMem; TyEq.sigma (hB x hx).ok.ty hB

theorem Ctx.IsTy.trunc {Γ A} (hA : IsTy Γ A) : IsTy Γ (.trunc A) :=
  have ⟨_, hA⟩ := hA; ⟨0, hA.trunc⟩

theorem Ctx.JEq.app_r {Γ} {A : Tm 0} {B : Tm 1} {f a f' a' Ba : Tm 0} {L : Finset String}
  (hB : ∀ x ∉ L, IsTy (Γ.cons x A) (B.open x))
  (hf : JEq Γ (A.pi B) f f') (ha : JEq Γ A a a') (hBa : TyEq Γ (B.lst a) Ba)
  : JEq Γ Ba (f.app a) (f'.app a') :=
  have ⟨_, hA⟩ := IsTy.top_cf hB
  have ⟨_, hB⟩ := IsTy.max_univ' hB
  .app_f hB hA hf ha hBa

syntax "ty_eq_constructor'" : tactic

macro_rules
  | `(tactic| ty_eq_constructor') => `(tactic| first
    | apply Ctx.IsTy.univ
    | apply Ctx.IsTy.empty
    | apply Ctx.IsTy.unit
    | apply Ctx.IsTy.nats
    | apply Ctx.TyEq.pi
    | apply Ctx.TyEq.sigma
  )

syntax "is_ty_constructor'" : tactic

macro_rules
  | `(tactic| is_ty_constructor') => `(tactic| first
    | apply Ctx.IsTy.univ
    | apply Ctx.IsTy.empty
    | apply Ctx.IsTy.unit
    | apply Ctx.IsTy.nats
    | apply Ctx.IsTy.pi
    | apply Ctx.IsTy.sigma
    | apply Ctx.IsTy.trunc
  )

theorem Ctx.JEq.regular {Γ A a b} (h : JEq Γ A a b) : IsTy Γ A := by induction h with
  | fv' hΓ hA => exact hΓ.ok.lookup hA
  | nil_ok => simp [*]
  | cons_ok =>
    simp only [IsTy.unit_iff, Ok.cons_iff, not_false_eq_true, true_and, *]
    constructor
    · apply JEq.ok; assumption
    · apply JEq.rhs_is_ty; assumption
  | _ =>
    first | assumption
          | apply JEq.lhs_is_ty; assumption
          | apply JEq.rhs_is_ty; assumption
          | (is_ty_constructor'
            <;> intros
            <;> (first | assumption | apply JEq.lhs_is_ty | apply Ctx.IsTy.ok)
            <;> apply_assumption
            <;> assumption)

theorem Ctx.JEq.ite_k {Γ A φ φ' l l' r r'}
  (hφ : JEq Γ (.univ 0) φ φ')
  (hl : JEq Γ A l l')
  (hr : JEq Γ A r r')
  : JEq Γ A (.ite φ l r) (.ite φ' l' r') :=
  have ⟨_, hA⟩ := hl.regular;
  .ite' (L := Γ.dv) hφ hA (fun _ hx => hl.wk0 hx hφ.lhs_is_ty)
                          (fun _ hx => hr.wk0 hx hφ.not.lhs_is_ty)

theorem Ctx.JEq.abs {Γ A A'} {B b b' : Tm 1} {ℓ} {L : Finset String}
  (hA : JEq Γ (.univ ℓ) A A')
  (hb : ∀ x ∉ L, JEq (Γ.cons x A) (B.open x) (b.open x) (b'.open x))
  : JEq Γ (.pi A B) (.abs A b) (.abs A' b')
  :=
  have ⟨_, h⟩ := IsTy.max_univ' (fun x hx => (hb x hx).regular);
  .abs' hA h hb
