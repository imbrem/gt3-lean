import Gt3.HasTy.Wk
import Gt3.JEq.Subst

inductive Ctx.S1 (Γ : Ctx) (σ : Tm.VSubst) : Ctx → Prop
  | nil : Ok Γ → S1 Γ σ .nil
  | cons' {Δ x A}
    : S1 Γ σ Δ
      → IsTy Γ (σ • A) → x ∉ Δ.dv → IsTy Δ A
      → HasTy Γ (σ • A) (σ.get x)
      → S1 Γ σ (Δ.cons x A)

theorem Ctx.S1.src_ok {Γ σ Δ} (h : S1 Γ σ Δ) : Ok Γ := by induction h <;> assumption

theorem Ctx.S1.trg_ok {Γ σ Δ} (h : S1 Γ σ Δ) : Ok Δ
  := by induction h <;> constructor <;> assumption

theorem Ctx.S1.tm {Γ σ Δ x A} (hσ : S1 Γ σ (.cons Δ x A)) : HasTy Γ (σ • A) (σ.get x)
  := by cases hσ; assumption

theorem Ctx.S1.refl {Γ σ Δ} (hσ : S1 Γ σ Δ) : SEq Γ σ σ Δ := by
  induction hσ <;> constructor <;> first | assumption | apply HasTy.refl; assumption

theorem Ctx.JEq.ls1 {Γ σ Δ A a b} (hσ : S1 Γ σ Δ) (h : JEq Δ A a b)
  : JEq Γ (σ • A) (σ • a) (σ • b) := h.ls1' hσ.refl

theorem Ctx.TyEq.ls1 {Γ σ Δ A B} (hσ : S1 Γ σ Δ) (h : TyEq Δ A B)
  : TyEq Γ (σ • A) (σ • B) := have ⟨_, h⟩ := h; ⟨_, h.ls1 hσ⟩

theorem Ctx.Lookup.s1 {Γ σ Δ} (hσ : S1 Γ σ Δ) {x A} (hx : Lookup Δ x A)
  : HasTy Γ (σ • A) (σ.get x) := by induction hx with
  | here => exact hσ.tm
  | there => apply_assumption; cases hσ; assumption

def Ctx.S1.src {Γ σ Δ} (_ : S1 Γ σ Δ) : Ctx := Γ

def Ctx.S1.trg {Γ σ Δ} (_ : S1 Γ σ Δ) : Ctx := Δ

theorem Ctx.S1.wk0 {Γ σ Δ x A}
  (h : S1 Γ σ Δ) (hx : x ∉ Γ.dv) (hA : IsTy Γ A)
  : S1 (Γ.cons x A) σ Δ := by
  induction h with
  | nil => constructor; constructor <;> assumption
  | cons' =>
    constructor <;> first
    | assumption
    | apply IsTy.wk0 <;> assumption
    | apply HasTy.wk0 <;> assumption

theorem Ctx.S1.lift_clamped {Γ σ Δ x A ℓ}
  (hσ : S1 Γ σ Δ) (hxΓ : x ∉ Γ.dv) (hxΔ : x ∉ Δ.dv)
  (hAΓ : HasTy Γ (.univ ℓ) (σ • A)) (hAΔ : HasTy Δ (.univ ℓ) A)
  (hx : σ.IdAt x)
  : S1 (Γ.cons x (σ • A)) σ (Δ.cons x A)
  :=
  have hAΓ := hAΓ.is_ty
  have hAΓ' := hAΓ.wk0 hxΓ hAΓ
  have hΓ : HasTy (Γ.cons x (σ • A)) (σ • A) (σ.get x) := by
    simp only [hx.get]
    constructor
    · exact hAΓ'.ok
    · exact .here _ _ _
  (hσ.wk0 hxΓ hAΓ).cons' hAΓ' hxΔ hAΔ.is_ty hΓ

theorem Ctx.HasTy.ls_clamped {K : Finset String} {Γ σ Δ} (hσ : S1 Γ σ Δ) {A a}
  (h : HasTy Δ A a) (hK : σ.Clamped K)
  : HasTy Γ (σ • A) (σ • a) := by induction h generalizing Γ with
  | fv _ hx => exact hx.s1 hσ
  | cast_level => apply cast_level; apply_assumption; assumption
  | cast => apply cast <;> (first | apply_assumption | apply TyEq.ls1) <;> assumption
  | _ =>
    constructor <;>
    first
    | (try simp only [<-Tm.smul_def, <-Tm.ls_lst])
      ; (first | apply_assumption | apply TyEq.ls1)
      <;> assumption
    | exact hσ.src_ok
    | {
      intro x hx
      rename Finset String => L
      have ⟨hxK, hxL, hxΓ, hxΔ⟩ : x ∉ K ∧ x ∉ L ∧ x ∉ hσ.src.dv ∧ x ∉ hσ.trg.dv
        := by simp only [<-Finset.notMem_union]; exact hx
      simp only [<-Tm.smul_def, Tm.open_ls_clamped (hv := hK) (hx := hxK)]
      apply_assumption
      <;> first | assumption | apply S1.lift_clamped
      <;> apply_assumption
      <;> assumption
    }

theorem Ctx.S1.castEqOn {Γ σ σ' Δ}
  (hστ : S1 Γ σ Δ) (hσ : σ.EqOn Δ.dv σ')
  : S1 Γ σ' Δ := by
  induction hστ with
  | nil => constructor; assumption
  | cons' _ _ _ hΔA =>
    have hΔA' := Finset.Subset.trans hΔA.scoped (Finset.subset_insert ?x _)
    (constructor <;> first
    | assumption
    | apply_assumption ; apply Tm.VSubst.EqOn.anti _ ‹_›
    | repeat first
      | rw [<-Tm.ls_eqOn_sub_fvs (h := hσ)]
      | rw [<-Tm.ls_eqOn_sub_fvs (h := hτ)]
      | rw [<-hσ.get _ Ctx.head_mem_dv]
      | rw [<-hτ.get _ Ctx.head_mem_dv]
      | assumption
    ) ; simp

theorem Ctx.S1.clamp {Γ σ Δ} (hσ : S1 Γ σ Δ) : S1 Γ (σ.clamp Δ.dv) Δ
  := hσ.castEqOn (σ.clamp_eqOn Δ.dv).symm

theorem Ctx.S1.unclamp {Γ σ Δ}
  (hσ : S1 Γ (σ.clamp Δ.dv) Δ)
  : S1 Γ σ Δ
  := hσ.castEqOn (σ.clamp_eqOn Δ.dv)

theorem Ctx.HasTy.ls {Γ σ Δ} (hσ : S1 Γ σ Δ) {A a} (h : HasTy Δ A a)
  : HasTy Γ (σ • A) (σ • a) := by
  convert (h.ls_clamped hσ.clamp (Tm.VSubst.clamped _ _)) using 1 <;>
  rw [Tm.ls_clamp_sub_fvs] <;>
  simp only [h.scoped_all]

theorem Ctx.S1.clamp_iff {Γ σ Δ}
  : S1 Γ (σ.clamp Δ.dv) Δ ↔ S1 Γ σ Δ
  := ⟨unclamp, clamp⟩

def Ctx.PSEq' (Γ Δ : Ctx) : Prop := S1 Γ 1 Δ

def Ctx.PSEq'.refl {Γ Δ} (h : PSEq' Γ Δ) : PSEq Γ Δ := S1.refl h

theorem Ctx.S1.one {Γ} (hΓ : Ok Γ) : S1 Γ 1 Γ := by
  induction hΓ with
  | nil => constructor; constructor
  | cons hΓ hx hA =>
    have hA' := hA.wk0 hx hA
    have hΓxA := hΓ.cons hx hA
    constructor <;> first | simp [HasTy.top_var_iff, *] | apply S1.wk0 <;> assumption

theorem Ctx.S1.rename_top' {Γ x y A B} (hx : x ∉ Γ.dv) (hy : y ∉ Γ.dv) (hAB : TyEq Γ A B)
  : S1 (Γ.cons x A) (.lset (.fv x) y) (Γ.cons y B) :=
  have hABt := hAB.top_var hx;
  have hxA := hAB.lhs.wk0 hx hAB.lhs
  have hxB := hAB.rhs.wk0 hx hAB.lhs
  have hAy := Finset.not_mem_subset hAB.lhs.scoped hy;
  have hBy := Finset.not_mem_subset hAB.rhs.scoped hy;
  have hAy' := Tm.ls_lset_not_mem (hx := hAy)
  have hBy' := Tm.ls_lset_not_mem (hx := hBy)
  by
    apply S1.cons' (.wk0
      ((S1.one hAB.ok).castEqOn
        (fun z hz => by simp [Tm.get_lset]; intro h; cases h; contradiction)
      ) hx hAB.lhs)
    <;> simp [hAB.rhs, *]

theorem Ctx.S1.rename_top {Γ x y A} (hx : x ∉ Γ.dv) (hy : y ∉ Γ.dv) (hA : IsTy Γ A)
  : S1 (Γ.cons x A) (.lset (.fv x) y) (Γ.cons y A) := rename_top' hx hy hA

theorem Ctx.HasTy.ps' {Γ Δ} (hσ : PSEq' Γ Δ) {A a} (h : HasTy Δ A a)
  : HasTy Γ A a := by convert h.ls hσ <;> simp

theorem Ctx.PSEq'.retype_top {Γ x A B} (hx : x ∉ Γ.dv) (hAB : TyEq Γ A B)
  : PSEq' (Γ.cons x A) (Γ.cons x B)
  := by convert (S1.rename_top' hx hx hAB) using 0; simp [Ctx.PSEq']

theorem Ctx.HasTy.cast_top {Γ x A B C a} (hAB : TyEq Γ A B) (h : HasTy (Γ.cons x B) C a)
  : HasTy (Γ.cons x A) C a := h.ps' (.retype_top h.ok.var hAB)

theorem Ctx.HasTy.cast_top' {Γ x ℓ A B C a} (hAB : JEq Γ (.univ ℓ) A B) (h : HasTy (Γ.cons x B) C a)
  : HasTy (Γ.cons x A) C a := h.cast_top hAB.ty_eq

theorem Ctx.HasTy.cast_top_symm' {Γ x ℓ A B C a}
  (hAB : JEq Γ (.univ ℓ) B A) (h : HasTy (Γ.cons x B) C a)
  : HasTy (Γ.cons x A) C a := h.cast_top' hAB.symm


-- theorem Ctx.HasTy.sjeq_clamped {K : Finset String} {Γ σ τ Δ} (hσ : SEq Γ σ τ Δ) {A a}
--   (h : HasTy Δ A a) (hK : σ.Clamped K)
--   : SJEq Γ σ τ A a := by induction h generalizing Γ with
--   | fv _ hx => exact hx.sjeq hσ
--   | cast_level =>
--     simp only [Ctx.SJEq, forall_and] at *
--     try casesm* _ ∧ _
--     constructor <;> apply JEq.cast_level <;> apply_assumption <;> assumption
--   | cast => stop apply cast <;> (first | apply_assumption | apply TyEq.ls1) <;> assumption
--   | _ =>
--     stop
--     constructor <;>
--     first
--     | (try simp only [<-Tm.smul_def, <-Tm.ls_lst])
--       ; (first | apply_assumption | apply TyEq.ls1)
--       <;> assumption
--     | exact hσ.src_ok
--     | {
--       intro x hx
--       rename Finset String => L
--       have ⟨hxK, hxL, hxΓ, hxΔ⟩ : x ∉ K ∧ x ∉ L ∧ x ∉ hσ.src.dv ∧ x ∉ hσ.trg.dv
--         := by simp only [<-Finset.notMem_union]; exact hx
--       simp only [<-Tm.smul_def, Tm.open_ls_clamped (hv := hK) (hx := hxK)]
--       apply_assumption
--       <;> first | assumption | apply S1.lift_clamped
--       <;> apply_assumption
--       <;> assumption
--     }
