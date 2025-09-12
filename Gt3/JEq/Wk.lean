import Gt3.JEq.Basic

structure Ctx.PSub (Γ Δ : Ctx) : Prop where
  left_ok : Ok Γ
  right_ok : Ok Δ
  is_perm : LSub Γ Δ

theorem Ctx.Ok.psub {Γ} (h : Ok Γ) : PSub Γ Γ := ⟨h, h, .refl Γ⟩

theorem Ctx.PSub.trans {Γ Δ Θ} (hΓΔ : PSub Γ Δ) (hΔΘ : PSub Δ Θ) : PSub Γ Θ where
  left_ok := hΓΔ.left_ok
  right_ok := hΔΘ.right_ok
  is_perm := hΓΔ.is_perm.trans hΔΘ.is_perm

theorem Ctx.PSub.dv {Γ Δ} (hΓΔ : PSub Γ Δ) : Δ.dv ⊆ Γ.dv := hΓΔ.is_perm.dv

theorem Ctx.PSub.cons' {Γ Δ} (h : PSub Γ Δ)
  {x A} (hx : x ∉ Γ.dv) (hΓA : IsTy Γ A) (hΔA : IsTy Δ A)
  : PSub (Γ.cons x A) (Δ.cons x A) where
  left_ok := h.left_ok.cons hx hΓA
  right_ok := h.right_ok.cons (Finset.not_mem_subset h.dv hx) hΔA
  is_perm := h.is_perm.cons x A

theorem Ctx.JEq.psub {Γ Δ} (h : PSub Γ Δ) {A a b : Tm 0} (hab : JEq Δ A a b)
  : JEq Γ A a b := by
  induction hab generalizing Γ with
  | nil_ok | cons_ok => exact .null h.left_ok
  | cast_level => apply cast_level; apply_assumption; assumption
  | cast' => apply cast' <;> apply_assumption <;> assumption
  | symm => apply symm; apply_assumption; assumption
  | trans => apply trans <;> apply_assumption <;> assumption
  | transfer' => apply transfer' <;> apply_assumption <;> assumption
  | _ =>
    constructor <;> first
    | apply_assumption <;> assumption
    | {
      rename Finset String => L
      intro x hx
      have ⟨hL, hΓ⟩ : x ∉ L ∧ x ∉ Γ.dv := by rw [<-Finset.notMem_union]; exact hx
      apply_assumption
      · exact hL
      · apply PSub.cons'
        <;> first | assumption | apply JEq.lhs_is_ty <;> apply_assumption <;> assumption
    }
    | apply h.is_perm; assumption

theorem Ctx.TyEq.psub {Γ Δ} (h : PSub Γ Δ) {A B : Tm 0} (hAB : TyEq Δ A B)
  : TyEq Γ A B := have ⟨ℓ, hAB⟩ := hAB; ⟨ℓ, hAB.psub h⟩

theorem Ctx.IsTy.psub {Γ Δ} (h : PSub Γ Δ) {A : Tm 0} (hA : IsTy Δ A)
  : IsTy Γ A := TyEq.psub h hA

theorem Ctx.PSub.cons {Γ Δ} (h : PSub Γ Δ)
  {x A} (hx : x ∉ Γ.dv) (hΔA : IsTy Δ A)
  : PSub (Γ.cons x A) (Δ.cons x A) where
  left_ok := h.left_ok.cons hx (hΔA.psub h)
  right_ok := h.right_ok.cons (Finset.not_mem_subset h.dv hx) hΔA
  is_perm := h.is_perm.cons x A

theorem Ctx.PSub.skip {Γ Δ} (h : PSub Γ Δ)
  {x A} (hx : x ∉ Γ.dv) (hΓA : IsTy Γ A)
  : PSub (Γ.cons x A) Δ where
  left_ok := h.left_ok.cons hx (hΓA)
  right_ok := h.right_ok
  is_perm := h.is_perm.skip (Finset.not_mem_subset h.dv hx) A

theorem Ctx.JEq.wk0 {Γ A a b} (hab : JEq Γ A a b) {x B} (hx : x ∉ Γ.dv) (hB : Γ.IsTy B)
  : JEq (Γ.cons x B) A a b
  := hab.psub (hab.ok.psub.skip hx hB)

theorem Ctx.TyEq.wk0 {Γ A B} (hAB : TyEq Γ A B) {x C} (hx : x ∉ Γ.dv) (hC : Γ.IsTy C)
  : TyEq (Γ.cons x C) A B
  := hAB.psub (hAB.ok.psub.skip hx hC)

theorem Ctx.TyEq.top_var' {Γ : Ctx} {x A B} (hx : x ∉ Γ.dv) (hAB : TyEq Γ A B)
  : JEq (Γ.cons x A) B (.fv x) (.fv x)
  := .cast (hAB.wk0 hx hAB.lhs) (.fv (hAB.ok.cons hx hAB.lhs) (.here _ _ _))

theorem Ctx.IsTy.wk0 {Γ A} (hA : IsTy Γ A) {x B} (hx : x ∉ Γ.dv) (hB : Γ.IsTy B)
  : IsTy (Γ.cons x B) A
  := hA.psub (hA.ok.psub.skip hx hB)

theorem Ctx.Ok.lookup {Γ x A} (h : Ok Γ) (hA : Lookup Γ x A) : IsTy Γ A
  := by induction hA <;> cases h <;> apply IsTy.wk0 <;> apply_assumption; assumption
