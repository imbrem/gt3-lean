import Gt3.JEq.Subst

theorem Ctx.JEq.to_cf {Γ : Ctx} {x} {A} {B a b : Tm 1}
  (h : JEq (Γ.cons x A) (B.open x) (a.open x) (b.open x))
  (hB : x ∉ B.fvs) (ha : x ∉ a.fvs) (hb : x ∉ b.fvs)
  : ∀ y ∉ Γ.dv , JEq (Γ.cons y A) (B.open y) (a.open y) (b.open y) := by
  intro y hy
  convert h.ls1 (SEq.rename_top hy h.ok.var h.ok.ty)
  <;> rw [Tm.ls_lset, Tm.lsv_open (hx := ‹_›), Tm.lst_fv]

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

theorem Ctx.IsTy.univ {Γ ℓ} (h : Ok Γ) : IsTy Γ (.univ ℓ) := ⟨ℓ + 1, .univ (.null h)⟩

theorem Ctx.IsTy.empty {Γ} (h : Ok Γ) : IsTy Γ .empty := ⟨0, .empty (.null h)⟩

theorem Ctx.IsTy.unit {Γ} (h : Ok Γ) : IsTy Γ .unit := ⟨0, .unit (.null h)⟩

@[simp] theorem Ctx.IsTy.univ_iff {Γ ℓ} : IsTy Γ (.univ ℓ) ↔ Ok Γ := ⟨IsTy.ok, IsTy.univ⟩

@[simp] theorem Ctx.IsTy.empty_iff {Γ} : IsTy Γ .empty ↔ Ok Γ := ⟨IsTy.ok, IsTy.empty⟩

@[simp] theorem Ctx.IsTy.unit_iff {Γ} : IsTy Γ .unit ↔ Ok Γ := ⟨IsTy.ok, IsTy.unit⟩

theorem Ctx.IsTy.pi {Γ A B} {L : Finset String}
  (hA : IsTy Γ A) (hB : ∀ x ∉ L, IsTy (Γ.cons x A) (B.open x)) : IsTy Γ (.pi A B)
  := by
  have ⟨m, hA⟩ := hA;
  have ⟨x, hx⟩ := (L ∪ B.fvs).exists_notMem;
  simp only [Finset.notMem_union] at hx
  have ⟨n, hB⟩ := hB x hx.left;
  have hB' := hB.to_cf_univ hx.right hx.right
  exists m ⊔ n ⊔ 1
  apply JEq.pi hA hB' <;> simp

syntax "is_ty_constructor'" : tactic

macro_rules
  | `(tactic| is_ty_constructor') => `(tactic| first
    | apply Ctx.IsTy.univ
    | apply Ctx.IsTy.empty
    | apply Ctx.IsTy.unit
    | apply Ctx.IsTy.pi
  )

theorem Ctx.JEq.regular {Γ A a b} (h : JEq Γ A a b) : IsTy Γ A := by induction h with
  | fv hΓ hA => exact hΓ.ok.lookup hA
  | nil_ok => simp [*]
  | cons_ok =>
    simp only [IsTy.unit_iff, Ok.cons_iff, not_false_eq_true, true_and, *]
    constructor
    · apply JEq.ok; assumption
    · apply JEq.rhs_is_ty; assumption
  | _ =>
    first | assumption
          | apply JEq.rhs_is_ty; assumption
          | (is_ty_constructor'
            <;> (first | assumption | apply JEq.lhs_is_ty | apply Ctx.IsTy.ok) <;> assumption)

-- theorem Ctx.JEq.cast_cmp {Γ A B a b} (h : JEq Γ A a b) (h' : Cmp Γ B a b) : JEq Γ B a b := by
--   induction h generalizing B with
--   | fv => exact h'.left
--   | univ => exact h'.left
--   | eqn =>
--     sorry
--   | _ => sorry
