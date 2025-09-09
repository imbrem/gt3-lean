import Gt3.JEq.Wk

inductive Ctx.SEq (Γ : Ctx) (σ τ : Tm.VSubst) : Ctx → Prop
  | nil : Ok Γ → SEq Γ σ τ .nil
  | cons' {Δ x A}
    : SEq Γ σ τ Δ
      → IsTy Γ (σ • A) → IsTy Γ (τ • A) → x ∉ Δ.dv → IsTy Δ A
      → JEq Γ (σ • A) (σ.get x) (τ.get x)
      → JEq Γ (τ • A) (σ.get x) (τ.get x)
      → SEq Γ σ τ (Δ.cons x A)

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

def Ctx.SEq.src {Γ σ τ Δ} (_ : SEq Γ σ τ Δ) : Ctx := Γ

def Ctx.SEq.trg {Γ σ τ Δ} (_ : SEq Γ σ τ Δ) : Ctx := Δ

theorem Ctx.JEq.ls1_clamped {K : Finset String} {Γ σ Δ} (hσ : SEq Γ σ σ Δ) {A a b}
  (h : JEq Δ A a b) (hK : σ.Clamped K)
  : JEq Γ (σ • A) (σ • a) (σ • b) := by induction h generalizing Γ with
  | fv _ hx _ => exact (hx.sjeq hσ).left
  | cast_level => apply cast_level; apply_assumption; assumption
  | cast => apply cast <;> apply_assumption <;> assumption
  | symm => apply symm; apply_assumption; assumption
  | trans => apply trans <;> apply_assumption <;> assumption
  | nil_ok => exact .null hσ.src_ok
  | cons_ok => apply_assumption; cases hσ; assumption
  | _ =>
    constructor <;>
    first
    | (try simp only [<-Tm.smul_def, <-Tm.ls_lst]) ; (apply_assumption <;> assumption)
    | {
      intro x hx
      rename Finset String => L
      have ⟨hxK, hxL, hxΓ, hxΔ⟩ : x ∉ K ∧ x ∉ L ∧ x ∉ hσ.src.dv ∧ x ∉ hσ.trg.dv
        := by simp only [<-Finset.notMem_union]; exact hx
      simp only [<-Tm.smul_def, Tm.open_ls_clamped (hv := hK) (hx := hxK)]
      apply_assumption
      <;> first | assumption | apply SEq.lift1_clamped
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

theorem Ctx.JEq.ls1 {Γ σ Δ} (hσ : SEq Γ σ σ Δ) {A a b} (h : JEq Δ A a b)
  : JEq Γ (σ • A) (σ • a) (σ • b) := by
  convert (h.ls1_clamped hσ.clamp (Tm.VSubst.clamped _ _)) using 1 <;>
  rw [Tm.ls_clamp_sub_fvs] <;>
  simp only [h.scoped_all]

theorem Ctx.SEq.clamp_iff {Γ σ τ Δ}
  : SEq Γ (σ.clamp Δ.dv) (τ.clamp Δ.dv) Δ ↔ SEq Γ σ τ Δ
  := ⟨unclamp, clamp⟩
