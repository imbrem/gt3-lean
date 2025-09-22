import Gt3.HasTy.Regular

theorem Ctx.HasTy.exists_pi_arg_general {Γ U A B P} (h : HasTy Γ U P) (hP : P = .pi A B)
  : ∃ℓ, HasTy Γ (.univ ℓ) A := by induction h with
  | pi hA => cases hP; exact ⟨_, hA⟩
  | _ => cases hP <;> apply_assumption <;> rfl

theorem Ctx.HasTy.exists_pi_res_general {Γ U A B P} (h : HasTy Γ U P) (hP : P = .pi A B)
  : ∃ℓ, ∀ x ∉ Γ.dv, HasTy (Γ.cons x A) (.univ ℓ) (B.open x) := by induction h with
  | pi _ hB => cases hP; exact ⟨_, top_quant_exact_k hB⟩
  | _ => cases hP <;> apply_assumption <;> rfl

theorem Ctx.HasTy.exists_pi_arg {Γ U A B} (h : HasTy Γ U (.pi A B))
  : ∃ℓ, HasTy Γ (.univ ℓ) A := exists_pi_arg_general h rfl

theorem Ctx.HasTy.exists_pi_res {Γ U A B} (h : HasTy Γ U (.pi A B))
  : ∃ℓ, ∀ x ∉ Γ.dv, HasTy (Γ.cons x A) (.univ ℓ) (B.open x) := exists_pi_res_general h rfl

theorem Ctx.HasTy.exists_sigma_arg_general {Γ U A B P} (h : HasTy Γ U P) (hP : P = .sigma A B)
  : ∃ℓ, HasTy Γ (.univ ℓ) A := by induction h with
  | sigma hA => cases hP; exact ⟨_, hA⟩
  | _ => cases hP <;> apply_assumption <;> rfl

theorem Ctx.HasTy.exists_sigma_res_general {Γ U A B P} (h : HasTy Γ U P) (hP : P = .sigma A B)
  : ∃ℓ, ∀ x ∉ Γ.dv, HasTy (Γ.cons x A) (.univ ℓ) (B.open x) := by induction h with
  | sigma _ hB => cases hP; exact ⟨_, top_quant_exact_k hB⟩
  | _ => cases hP <;> apply_assumption <;> rfl

theorem Ctx.HasTy.exists_sigma_arg {Γ U A B} (h : HasTy Γ U (.sigma A B))
  : ∃ℓ, HasTy Γ (.univ ℓ) A := exists_sigma_arg_general h rfl

theorem Ctx.HasTy.exists_sigma_res {Γ U A B} (h : HasTy Γ U (.sigma A B))
  : ∃ℓ, ∀ x ∉ Γ.dv, HasTy (Γ.cons x A) (.univ ℓ) (B.open x) := exists_sigma_res_general h rfl

theorem Ctx.HasTy.regular_pi_arg_ty {Γ A B f} (h : HasTy Γ (.pi A B) f)
  : ∃ℓ, HasTy Γ (.univ ℓ) A := have ⟨_, h⟩ := h.regular.has_ty; h.exists_pi_arg

theorem Ctx.HasTy.regular_pi_res_ty {Γ A B f} (h : HasTy Γ (.pi A B) f)
  : ∃ℓ, ∀ x ∉ Γ.dv, HasTy (Γ.cons x A) (.univ ℓ) (B.open x)
  := have ⟨_, h⟩ := h.regular.has_ty; h.exists_pi_res

theorem Ctx.HasTy.regular_sigma_arg_ty {Γ A B p} (h : HasTy Γ (.sigma A B) p)
  : ∃ℓ, HasTy Γ (.univ ℓ) A := have ⟨_, h⟩ := h.regular.has_ty; h.exists_sigma_arg

theorem Ctx.HasTy.regular_sigma_res_ty {Γ A B p} (h : HasTy Γ (.sigma A B) p)
  : ∃ℓ, ∀ x ∉ Γ.dv, HasTy (Γ.cons x A) (.univ ℓ) (B.open x)
  := have ⟨_, h⟩ := h.regular.has_ty; h.exists_sigma_res

theorem Ctx.HasTy.app_e {Γ} {A : Tm 0} {B : Tm 1} {f a : Tm 0}
    (hf : HasTy Γ (A.pi B) f) (ha : HasTy Γ A a) : HasTy Γ (B.lst a) (f.app a)
    :=
    have ⟨_, hA⟩ := hf.regular_pi_arg_ty
    have ⟨_, hB⟩ := hf.regular_pi_res_ty
    .app' hB hA hf ha (IsTy.lst_cf' (fun x hx => (hB x hx).is_ty) ha.refl)

theorem Ctx.HasTy.app {Γ} {A : Tm 0} {B : Tm 1} {f a Ba : Tm 0}
    (hf : HasTy Γ (A.pi B) f) (ha : HasTy Γ A a)
    (hBa : TyEq Γ (B.lst a) Ba)
    : HasTy Γ Ba (f.app a)
    := (hf.app_e ha).cast hBa

theorem Ctx.HasTy.of_has_ty_general {Γ U A a P} (h : HasTy Γ U P) (hP : P = .has_ty A a)
  : HasTy Γ A a := by induction h with
  | m_has_ty' hA ha => cases hP; exact ha
  | _ => cases hP <;> apply_assumption <;> rfl

theorem Ctx.HasTy.of_has_ty {Γ U A a} (h : HasTy Γ U (.has_ty A a)) : HasTy Γ A a
  := of_has_ty_general h rfl

theorem Ctx.HasTy.m_has_ty_iff {Γ A a} : HasTy Γ .unit (.has_ty A a) ↔ HasTy Γ A a
  := ⟨of_has_ty, m_has_ty⟩

theorem Ctx.IsWf.to_has_ty {Γ A a} (h : IsWf Γ (.has_ty A a)) : HasTy Γ A a
  := have ⟨_, h⟩ := h.has_ty; h.of_has_ty

theorem Ctx.HasTy.wf_iff {Γ A a} : IsWf Γ (.has_ty A a) ↔ HasTy Γ A a
  := ⟨IsWf.to_has_ty, fun h => (m_has_ty h).is_wf⟩
