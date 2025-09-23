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

macro "psub_tactic_helper" h:ident Γ:ident : tactic =>
  `(tactic| first
    | apply_assumption <;> assumption
    | {
      rename Finset String => L
      intro x hx
      have ⟨hL, hΓ⟩ : x ∉ L ∧ x ∉ ($Γ).dv := by rw [<-Finset.notMem_union]; exact hx
      apply_assumption
      · exact hL
      · apply ($h).cons' hΓ
        <;> (first | assumption | apply Ctx.IsTy.not | apply Ctx.JEq.lhs_is_ty)
        <;> (first | apply Ctx.JEq.nats | apply Ctx.JEq.unit | apply Ctx.JEq.empty
                   | apply_assumption)
        <;> first | assumption | exact ($h).left_ok | exact ($h).right_ok
    }
    | apply ($h).is_perm; assumption
  )

theorem Ctx.JEq.psub {Γ Δ} (h : PSub Γ Δ) {A a b : Tm 0} (hab : JEq Δ A a b)
  : JEq Γ A a b := by
  induction hab generalizing Γ with
  | nil_ok | cons_ok => exact .null h.left_ok
  | cast_level => apply cast_level; apply_assumption; assumption
  | cast' => apply cast' <;> apply_assumption <;> assumption
  | symm => apply symm; apply_assumption; assumption
  | trans => apply trans <;> apply_assumption <;> assumption
  | transfer' => apply transfer' <;> apply_assumption <;> assumption
  | eqn_rfl => apply eqn_rfl <;> psub_tactic_helper h Γ
  | prop_inhab_unit' => apply prop_inhab_unit' <;> psub_tactic_helper h Γ
  | _ => constructor <;> psub_tactic_helper h Γ

theorem Ctx.TyEq.psub {Γ Δ} (h : PSub Γ Δ) {A B : Tm 0} (hAB : TyEq Δ A B)
  : TyEq Γ A B := have ⟨ℓ, hAB⟩ := hAB; ⟨ℓ, hAB.psub h⟩

theorem Ctx.IsTy.psub {Γ Δ} (h : PSub Γ Δ) {A : Tm 0} (hA : IsTy Δ A)
  : IsTy Γ A := TyEq.psub h hA

theorem Ctx.WfEq.psub {Γ Δ} (h : PSub Γ Δ) {a b : Tm 0} (hab : WfEq Δ a b)
  : WfEq Γ a b := have ⟨A, hab⟩ := hab; ⟨A, hab.psub h⟩

theorem Ctx.IsWf.psub {Γ Δ} (h : PSub Γ Δ) {a : Tm 0} (ha : IsWf Δ a)
  : IsWf Γ a := WfEq.psub h ha

theorem Ctx.IsUniv.psub {Γ Δ} (h : PSub Γ Δ) {A : Tm 0} (hA : IsUniv Δ A)
  : IsUniv Γ A := have ⟨ℓ, hA⟩ := hA; ⟨ℓ, hA.psub h⟩

theorem Ctx.IsInhab.psub {Γ Δ} (h : PSub Γ Δ) {A : Tm 0} (hA : IsInhab Δ A)
  : IsInhab Γ A := have ⟨a, hA⟩ := hA; ⟨a, hA.psub h⟩

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

theorem Ctx.WfEq.wk0 {Γ a b} (hab : WfEq Γ a b) {x A} (hx : x ∉ Γ.dv) (hA : Γ.IsTy A)
  : WfEq (Γ.cons x A) a b
  := have ⟨A, hab⟩ := hab; ⟨A, hab.wk0 hx hA⟩

theorem Ctx.IsWf.wk0 {Γ a} (ha : IsWf Γ a) {x A} (hx : x ∉ Γ.dv) (hA : Γ.IsTy A)
  : IsWf (Γ.cons x A) a
  := WfEq.wk0 ha hx hA

theorem Ctx.Ok.lookup {Γ x A} (h : Ok Γ) (hA : Lookup Γ x A) : IsTy Γ A
  := by induction hA <;> cases h <;> apply IsTy.wk0 <;> apply_assumption; assumption

theorem Ctx.JEq.arr {Γ A A' B B' n m ℓ}
  (hA : JEq Γ (.univ n) A A') (hB : JEq Γ (.univ m) B B')
  (hn : n ≤ ℓ) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ)
  : JEq Γ (.univ ℓ) (.arr A B) (.arr A' B')
  := .pi (L := Γ.dv) hA (fun x hx => (by convert hB.wk0 hx hA.lhs_is_ty <;> simp)) hn hm hℓ

theorem Ctx.JEq.prod {Γ A A' B B' n m ℓ}
  (hA : JEq Γ (.univ n) A A') (hB : JEq Γ (.univ m) B B')
  (hn : n ≤ ℓ) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ)
  : JEq Γ (.univ ℓ) (.prod A B) (.prod A' B')
  := .sigma (L := Γ.dv) hA (fun x hx => (by convert hB.wk0 hx hA.lhs_is_ty <;> simp)) hn hm hℓ

theorem Ctx.JEq.wk1 {Γ : Ctx} {x A B a b}
  (hab : JEq (Γ.cons x A) B a b) {y C} (hy : y ∉ insert x Γ.dv) (hC : Γ.IsTy C)
  : JEq ((Γ.cons y C).cons x A) B a b
  := by
  simp at hy
  exact hab.psub ((hC.ok.psub.skip hy.2 hC).cons (by simp [Ne.symm hy.1, hab.ok.var]) hab.ok.ty)
