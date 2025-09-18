import Gt3.JEq.Wk

inductive Ctx.SEq (Γ : Ctx) (σ τ : Tm.VSubst) : Ctx → Prop
  | nil : Ok Γ → SEq Γ σ τ .nil
  | cons' {Δ x A}
    : SEq Γ σ τ Δ
      → IsTy Γ (σ • A) → IsTy Γ (τ • A) → x ∉ Δ.dv → IsTy Δ A
      → JEq Γ (σ • A) (σ.get x) (τ.get x)
      → JEq Γ (τ • A) (σ.get x) (τ.get x)
      → SEq Γ σ τ (Δ.cons x A)

def Ctx.PSEq (Γ Δ : Ctx) : Prop := SEq Γ 1 1 Δ

theorem Ctx.SEq.src_ok {Γ σ τ Δ} (h : SEq Γ σ τ Δ) : Ok Γ := by induction h <;> assumption

theorem Ctx.SEq.trg_ok {Γ σ τ Δ} (h : SEq Γ σ τ Δ) : Ok Δ
  := by induction h <;> constructor <;> assumption

theorem Ctx.SEq.symm {Γ σ τ Δ} (h : SEq Γ σ τ Δ) : SEq Γ τ σ Δ
  := by induction h <;> constructor <;> repeat first | assumption | apply JEq.symm

def Ctx.SJEq (Γ : Ctx) (σ τ : Tm.VSubst) (A a : Tm 0) : Prop
  := JEq Γ (σ • A) (σ • a) (τ • a) ∧ JEq Γ (τ • A) (σ • a) (τ • a)

theorem Ctx.SJEq.left {Γ σ τ A a} (hσ : SJEq Γ σ τ A a) : JEq Γ (σ • A) (σ • a) (τ • a)
  := And.left hσ

theorem Ctx.SJEq.right {Γ σ τ A a} (hσ : SJEq Γ σ τ A a) : JEq Γ (τ • A) (σ • a) (τ • a)
  := And.right hσ

theorem Ctx.SJEq.symm {Γ σ τ A a} (hσ : SJEq Γ σ τ A a) : SJEq Γ τ σ A a
  := ⟨hσ.right.symm, hσ.left.symm⟩

theorem Ctx.SEq.tm {Γ σ τ Δ x A} (hσ : SEq Γ σ τ (.cons Δ x A)) : SJEq Γ σ τ A (.fv x)
  := by cases hσ; constructor <;> assumption

theorem Ctx.Lookup.sjeq {Γ σ τ Δ} (hσ : SEq Γ σ τ Δ) {x A} (hx : Lookup Δ x A)
  : SJEq Γ σ τ A (.fv x) := by induction hx with
  | here => exact hσ.tm
  | there => apply_assumption; cases hσ; assumption

theorem cofinite_weakening_helper.{u} {α : Type u}
  [DecidableEq α] {L K : Finset α} {P : α → Prop}
  : (∀x ∉ L , P x) ↔ (∀ x , (x ∉ L → P x) ∧ ((x ∉ L ∧ x ∉ K) → P x))
  := ⟨fun h x => ⟨fun hx => h x hx, fun ⟨hx, _⟩ => h x hx⟩, fun h x hx => (h x).left hx⟩

theorem Ctx.SEq.wk0 {Γ σ τ Δ x A}
  (h : SEq Γ σ τ Δ) (hx : x ∉ Γ.dv) (hA : IsTy Γ A)
  : SEq (Γ.cons x A) σ τ Δ := by
  induction h with
  | nil => constructor; constructor <;> assumption
  | cons' =>
    constructor <;> first
    | assumption
    | apply IsTy.wk0 <;> assumption
    | apply JEq.wk0 <;> assumption

theorem Ctx.SEq.lift1_clamped {Γ σ Δ x A A' ℓ}
  (hσ : SEq Γ σ σ Δ) (hxΓ : x ∉ Γ.dv) (hxΔ : x ∉ Δ.dv)
  (hAΓ : JEq Γ (.univ ℓ) (σ • A) (σ • A')) (hAΔ : JEq Δ (.univ ℓ) A A')
  (hx : σ.IdAt x)
  : SEq (Γ.cons x (σ • A)) σ σ (Δ.cons x A)
  :=
  have hAΓ := hAΓ.lhs_is_ty
  have hAΓ' := hAΓ.wk0 hxΓ hAΓ
  have hΓ : JEq (Γ.cons x (σ • A)) (σ • A) (σ.get x) (σ.get x) := by
    simp only [hx.get]
    constructor
    · exact .null hAΓ'.ok
    · exact .here _ _ _
  (hσ.wk0 hxΓ hAΓ).cons' hAΓ' hAΓ' hxΔ hAΔ.lhs_is_ty
  hΓ hΓ

theorem Ctx.SEq.lift1_not_clamped {Γ σ Δ x φ φ'}
  (hσ : SEq Γ σ σ Δ) (hxΓ : x ∉ Γ.dv) (hxΔ : x ∉ Δ.dv)
  (hφΓ : JEq Γ (.univ 0) (σ • φ) (σ • φ')) (hφΔ : JEq Δ (.univ 0) φ φ')
  (hx : σ.IdAt x)
  : SEq (Γ.cons x (σ • φ).not) σ σ (Δ.cons x φ.not)
  := lift1_clamped hσ hxΓ hxΔ hφΓ.not hφΔ.not hx

theorem Ctx.SEq.lift1_nat_clamped {Γ σ Δ x}
  (hσ : SEq Γ σ σ Δ) (hxΓ : x ∉ Γ.dv) (hxΔ : x ∉ Δ.dv)
  (hx : σ.IdAt x)
  : SEq (Γ.cons x .nats) σ σ (Δ.cons x .nats)
  := Ctx.SEq.lift1_clamped hσ hxΓ hxΔ (.nats hσ.src_ok) (.nats hσ.trg_ok) hx

theorem Ctx.SEq.lift1_unit_clamped {Γ σ Δ x}
  (hσ : SEq Γ σ σ Δ) (hxΓ : x ∉ Γ.dv) (hxΔ : x ∉ Δ.dv)
  (hx : σ.IdAt x)
  : SEq (Γ.cons x .unit) σ σ (Δ.cons x .unit)
  := Ctx.SEq.lift1_clamped (ℓ := 0) hσ hxΓ hxΔ (.unit hσ.src_ok) (.unit hσ.trg_ok) hx

theorem Ctx.SEq.lift1_not_empty_clamped {Γ σ Δ x}
  (hσ : SEq Γ σ σ Δ) (hxΓ : x ∉ Γ.dv) (hxΔ : x ∉ Δ.dv)
  (hx : σ.IdAt x)
  : SEq (Γ.cons x Tm.empty.not) σ σ (Δ.cons x Tm.empty.not)
  := Ctx.SEq.lift1_clamped
    (ℓ := 0) hσ hxΓ hxΔ (.not (.empty hσ.src_ok)) (.not (.empty hσ.trg_ok)) hx

def Ctx.SEq.src {Γ σ τ Δ} (_ : SEq Γ σ τ Δ) : Ctx := Γ

def Ctx.SEq.trg {Γ σ τ Δ} (_ : SEq Γ σ τ Δ) : Ctx := Δ

theorem Ctx.JEq.subst_open_cofinite_k_clamped_helper {L : Finset String} {Γ : Ctx} {σ : Tm.VSubst}
  (hL : σ.Clamped L) {A B : Tm 0} {b b' : Tm 1}
  {x} (hx : x ∉ L) (h : JEq (Γ.cons x A) B (σ • b.open x) (σ • b'.open x))
  : JEq (Γ.cons x A) B ((σ • b).open x) ((σ • b').open x)
  := by convert h using 1 <;> rw [Tm.open_ls_clamped (hv := hL) (hx := hx)]

theorem Ctx.JEq.subst_open_cofinite_clamped_helper {L : Finset String} {Γ : Ctx} {σ : Tm.VSubst}
  (hL : σ.Clamped L) {A : Tm 0} {B b b' : Tm 1}
  {x} (hx : x ∉ L) (h : JEq (Γ.cons x A) (σ • B.open x) (σ • b.open x) (σ • b'.open x))
  : JEq (Γ.cons x A) ((σ • B).open x) ((σ • b).open x) ((σ • b').open x)
  := by convert h using 1 <;> rw [Tm.open_ls_clamped (hv := hL) (hx := hx)]

theorem Tm.smul_lst {k} (v : VSubst) (t : Tm (k + 1)) : v • (t.lst .zero) = (v • t).lst .zero
  := by rw [Tm.ls_lst, Tm.smul_zero]

theorem Ctx.JEq.ls1_clamped {K : Finset String} {Γ σ Δ} (hσ : SEq Γ σ σ Δ) {A a b}
  (h : JEq Δ A a b) (hK : σ.Clamped K)
  : JEq Γ (σ • A) (σ • a) (σ • b) := by induction h generalizing Γ with
  | fv' _ hx _ => exact (hx.sjeq hσ).left
  | cast_level => apply cast_level; apply_assumption; assumption
  | cast' => apply cast' <;> apply_assumption <;> assumption
  | symm => apply symm; apply_assumption; assumption
  | trans => apply trans <;> apply_assumption <;> assumption
  | transfer' => apply transfer' <;> apply_assumption <;> assumption
  | nil_ok => exact .null hσ.src_ok
  | cons_ok => apply_assumption; cases hσ; assumption
  | _ =>
    constructor <;>
    first
    | (try simp only [<-Tm.smul_def, <-Tm.ls_lst, <-Tm.smul_fst, <-Tm.smul_lst, <-Tm.ls_lst_null])
      ; (apply_assumption <;> assumption)
    | {
      intro x hx
      rename Finset String => L
      have ⟨hxK, hxL, hxΓ, hxΔ⟩ : x ∉ K ∧ x ∉ L ∧ x ∉ hσ.src.dv ∧ x ∉ hσ.trg.dv
        := by simp only [<-Finset.notMem_union]; exact hx
      first | apply subst_open_cofinite_clamped_helper | apply subst_open_cofinite_k_clamped_helper
      · exact hK
      · exact hxK
      · (try simp only [<-Tm.smul_def, <-Tm.smul_succArrow_open (hx := hK x hxK)])
        apply_assumption
        <;> (first  | assumption
                    | apply SEq.lift1_clamped
                    | apply SEq.lift1_not_clamped
                    | apply SEq.lift1_nat_clamped
                    | apply SEq.lift1_unit_clamped
                    | apply SEq.lift1_not_empty_clamped)
        <;> apply_assumption
        <;> assumption
    }

theorem Ctx.SEq.castEqOn {Γ σ τ σ' τ' Δ}
  (hστ : SEq Γ σ τ Δ) (hσ : σ.EqOn Δ.dv σ') (hτ : τ.EqOn Δ.dv τ')
  : SEq Γ σ' τ' Δ := by
  induction hστ with
  | nil => constructor; assumption
  | cons' _ _ _ _ hΔA =>
    have hΔA' := Finset.Subset.trans hΔA.scoped (Finset.subset_insert ?x _)
    (constructor <;> first
    | assumption
    | apply_assumption <;> apply Tm.VSubst.EqOn.anti _ ‹_›
    | repeat first
      | rw [<-Tm.ls_eqOn_sub_fvs (h := hσ)]
      | rw [<-Tm.ls_eqOn_sub_fvs (h := hτ)]
      | rw [<-hσ.get _ Ctx.head_mem_dv]
      | rw [<-hτ.get _ Ctx.head_mem_dv]
      | assumption
    ) <;> simp

theorem Ctx.SEq.clamp {Γ σ τ Δ} (hσ : SEq Γ σ τ Δ) : SEq Γ (σ.clamp Δ.dv) (τ.clamp Δ.dv) Δ
  := hσ.castEqOn (σ.clamp_eqOn Δ.dv).symm (τ.clamp_eqOn Δ.dv).symm

theorem Ctx.SEq.unclamp {Γ σ τ Δ}
  (hσ : SEq Γ (σ.clamp Δ.dv) (τ.clamp Δ.dv) Δ)
  : SEq Γ σ τ Δ
  := hσ.castEqOn (σ.clamp_eqOn Δ.dv) (τ.clamp_eqOn Δ.dv)

theorem Ctx.JEq.ls1' {Γ σ Δ} (hσ : SEq Γ σ σ Δ) {A a b} (h : JEq Δ A a b)
  : JEq Γ (σ • A) (σ • a) (σ • b) := by
  convert (h.ls1_clamped hσ.clamp (Tm.VSubst.clamped _ _)) using 1 <;>
  rw [Tm.ls_clamp_sub_fvs] <;>
  simp only [h.scoped_all]

theorem Ctx.SEq.clamp_iff {Γ σ τ Δ}
  : SEq Γ (σ.clamp Δ.dv) (τ.clamp Δ.dv) Δ ↔ SEq Γ σ τ Δ
  := ⟨unclamp, clamp⟩

theorem Ctx.SEq.one {Γ} (hΓ : Ok Γ) : SEq Γ 1 1 Γ := by
  induction hΓ with
  | nil => constructor; constructor
  | cons hΓ hx hA =>
    have hA' := hA.wk0 hx hA
    have hΓxA := hΓ.cons hx hA
    constructor <;> first | simp [JEq.top_var_iff, *] | apply SEq.wk0 <;> assumption

theorem Ctx.SEq.one_iff {Γ} : SEq Γ 1 1 Γ ↔ Ok Γ := ⟨SEq.src_ok, SEq.one⟩

theorem Ctx.IsTy.wk0_lset {Γ x A B} (hA : IsTy Γ A) (hx : x ∉ Γ.dv) (hB : IsTy Γ B) (t : Tm 0)
  : IsTy (Γ.cons x B) ((t.lset x) • A) := by
  convert hA.wk0 hx hB; rw [Tm.ls_eqOn_fvs, Tm.ls_one]
  intro z hz; simp [Tm.get_lset]; intro h; cases h
  exact (hx (hA.scoped hz)).elim


theorem Ctx.SEq.lset {Γ x y} (hΓ : Ok Γ) (hx : x ∉ Γ.dv) (hy : y ∉ Γ.dv) (a b : Tm 0)
  : SEq Γ (.lset a x) (.lset b y) Γ :=
  (SEq.one hΓ).castEqOn
        (fun z hz => by simp [Tm.get_lset]; intro h; cases h; contradiction)
        (fun z hz => by simp [Tm.get_lset]; intro h; cases h; contradiction)

theorem Ctx.SEq.lset₁ {Γ x} (hΓ : Ok Γ) (hx : x ∉ Γ.dv) (a : Tm 0)
  : SEq Γ (.lset a x) (.lset a x) Γ := lset hΓ hx hx a a

theorem Ctx.SEq.rename_top' {Γ x y A B} (hx : x ∉ Γ.dv) (hy : y ∉ Γ.dv) (hAB : TyEq Γ A B)
  : SEq (Γ.cons x A) (.lset (.fv x) y) (.lset (.fv x) y) (Γ.cons y B) :=
  have hABt := hAB.top_var' hx;
  have hxA := hAB.lhs.wk0 hx hAB.lhs
  have hxB := hAB.rhs.wk0 hx hAB.lhs
  have hAy' := Tm.ls_lset_not_mem (hx := Finset.not_mem_subset hAB.lhs.scoped hy)
  have hBy' := Tm.ls_lset_not_mem (hx := Finset.not_mem_subset hAB.rhs.scoped hy)
  by
    apply SEq.cons' (.wk0 (.lset₁ hAB.ok hy (.fv x)) hx hAB.lhs)
    <;> simp [hAB.rhs, *]

theorem Ctx.SEq.rename_top {Γ x y A} (hx : x ∉ Γ.dv) (hy : y ∉ Γ.dv) (hA : IsTy Γ A)
  : SEq (Γ.cons x A) (.lset (.fv x) y) (.lset (.fv x) y) (Γ.cons y A) := rename_top' hx hy hA

theorem Ctx.JEq.ps {Γ Δ} (hσ : PSEq Γ Δ) {A a b} (h : JEq Δ A a b)
  : JEq Γ A a b := by convert h.ls1' hσ <;> simp

theorem Ctx.PSEq.retype_top {Γ x A B} (hx : x ∉ Γ.dv) (hAB : TyEq Γ A B)
  : PSEq (Γ.cons x A) (Γ.cons x B)
  := by convert (SEq.rename_top' hx hx hAB) using 0; simp [Ctx.PSEq]

theorem Ctx.JEq.cast_top {Γ x A B C a b} (hAB : TyEq Γ A B) (h : JEq (Γ.cons x B) C a b)
  : JEq (Γ.cons x A) C a b := h.ps (.retype_top h.ok.var hAB)

theorem Ctx.JEq.cast_top' {Γ x ℓ A B C a b} (hAB : JEq Γ (.univ ℓ) A B) (h : JEq (Γ.cons x B) C a b)
  : JEq (Γ.cons x A) C a b := h.cast_top hAB.ty_eq
