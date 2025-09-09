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
