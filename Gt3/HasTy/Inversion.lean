import Gt3.HasTy.Regular

def Ctx.HasTyUnder (Γ : Ctx) (A : Tm 0) (B b : Tm 1) : Prop
  := ∀ x ∉ Γ.dv, HasTy (Γ.cons x A) (B.open x) (b.open x)

def Ctx.IsWfUnder (Γ : Ctx) (A : Tm 0) (B : Tm 1) : Prop
  := ∀ x ∉ Γ.dv, IsWf (Γ.cons x A) (B.open x)

def Ctx.IsTyUnder (Γ : Ctx) (A : Tm 0) (B : Tm 1) : Prop
  := ∀ x ∉ Γ.dv, IsTy (Γ.cons x A) (B.open x)

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

theorem Ctx.IsWf.exists_pi_arg {Γ A B} (h : IsWf Γ (.pi A B))
  : ∃ℓ, HasTy Γ (.univ ℓ) A := have ⟨_, h⟩ := h.has_ty; h.exists_pi_arg

theorem Ctx.IsWf.exists_pi_res {Γ A B} (h : IsWf Γ (.pi A B))
  : ∃ℓ, ∀ x ∉ Γ.dv, HasTy (Γ.cons x A) (.univ ℓ) (B.open x)
  := have ⟨_, h⟩ := h.has_ty; h.exists_pi_res

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

theorem Ctx.IsWf.exists_sigma_arg {Γ A B} (h : IsWf Γ (.sigma A B))
  : ∃ℓ, HasTy Γ (.univ ℓ) A := have ⟨_, h⟩ := h.has_ty; h.exists_sigma_arg

theorem Ctx.IsWf.exists_sigma_res {Γ A B} (h : IsWf Γ (.sigma A B))
  : ∃ℓ, ∀ x ∉ Γ.dv, HasTy (Γ.cons x A) (.univ ℓ) (B.open x)
  := have ⟨_, h⟩ := h.has_ty; h.exists_sigma_res

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

theorem Ctx.HasTy.fst {Γ A B p}
  (hp : HasTy Γ (.sigma A B) p) : HasTy Γ A (p.fst) :=
  have ⟨_, hA⟩ := hp.regular_sigma_arg_ty
  have ⟨_, hB⟩ := hp.regular_sigma_res_ty
  .fst' hB hA hp

theorem Ctx.HasTy.snd {Γ A B p}
  (hp : HasTy Γ (.sigma A B) p) : HasTy Γ (B.lst (p.fst)) (p.snd) :=
  have ⟨_, hA⟩ := hp.regular_sigma_arg_ty
  have ⟨_, hB⟩ := hp.regular_sigma_res_ty
  .snd' hB hA hp (IsTy.lst_cf' (fun x hx => (hB x hx).is_ty) (HasTy.fst hp).refl)

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

theorem Ctx.HasTy.trunc_is_ty_general {Γ U A P} (h : HasTy Γ U P) (hP : P = .trunc A)
  : IsTy Γ A := by induction h with
  | trunc hA => cases hP; exact ⟨_, hA.refl⟩
  | _ => cases hP <;> apply_assumption <;> rfl

theorem Ctx.HasTy.trunc_is_ty {Γ U A} (h : HasTy Γ U (.trunc A)) : IsTy Γ A
  := trunc_is_ty_general h rfl

theorem Ctx.IsWf.trunc_is_ty {Γ A} (h : IsWf Γ (.trunc A)) : IsTy Γ A
  := have ⟨_, h⟩ := h.has_ty; h.trunc_is_ty

theorem Ctx.IsWf.trunc {Γ A} (h : IsTy Γ A) : IsWf Γ (.trunc A)
  := have ⟨_, h⟩ := h; ⟨_, h.trunc⟩

theorem Ctx.IsWf.trunc_wf_iff {Γ A} : IsWf Γ (.trunc A) ↔ IsTy Γ A
  := ⟨trunc_is_ty, trunc⟩

theorem Ctx.HasTy.exists_app_general {Γ U f a P} (h : HasTy Γ U P) (hP : P = .app f a)
  : ∃A B, HasTy Γ (.pi A B) f ∧ HasTy Γ A a := by induction h with
  | app' _ _ hf ha _ => cases hP; exact ⟨_, _, hf, ha⟩
  | _ => cases hP <;> apply_assumption <;> rfl

theorem Ctx.HasTy.exists_app {Γ U f a} (h : HasTy Γ U (.app f a))
  : ∃A B, HasTy Γ (.pi A B) f ∧ HasTy Γ A a := exists_app_general h rfl

theorem Ctx.HasTy.exists_abs_general {Γ U A b P} (h : HasTy Γ U P) (hP : P = .abs A b)
  : ∃B : Tm 1, ∀ x ∉ Γ.dv, HasTy (Γ.cons x A) (B.open x) (b.open x) := by
  induction h with
  | abs' hA _ hb => cases hP; exact ⟨_, HasTy.top_quant_exact hb⟩
  | _ => cases hP <;> apply_assumption <;> rfl

theorem Ctx.HasTy.exists_abs {Γ U A b} (h : HasTy Γ U (.abs A b))
  : ∃B : Tm 1, HasTyUnder Γ A B b
  := exists_abs_general h rfl

theorem Ctx.IsWf.exists_abs {Γ A b} (h : IsWf Γ (.abs A b))
  : ∃B : Tm 1, HasTyUnder Γ A B b
  := have ⟨_, h⟩ := h.has_ty; h.exists_abs

theorem Ctx.HasTy.exists_fst_general {Γ U p P} (h : HasTy Γ U P) (hp : P = .fst p)
  : ∃A B, HasTy Γ (.sigma A B) p := by induction h with
  | fst' _ _ hp => cases hp; exact ⟨_, _, hp⟩
  | _ => cases hp <;> apply_assumption <;> rfl

theorem Ctx.HasTy.exists_fst {Γ U p} (h : HasTy Γ U (.fst p))
  : ∃A B, HasTy Γ (.sigma A B) p := exists_fst_general h rfl

theorem Ctx.HasTy.exists_snd_general {Γ U p P} (h : HasTy Γ U P) (hp : P = .snd p)
  : ∃A B, HasTy Γ (.sigma A B) p := by induction h with
  | snd' _ _ hp => cases hp; exact ⟨_, _, hp⟩
  | _ => cases hp <;> apply_assumption <;> rfl

theorem Ctx.HasTy.exists_snd {Γ U p} (h : HasTy Γ U (.snd p))
  : ∃A B, HasTy Γ (.sigma A B) p := exists_snd_general h rfl

theorem Ctx.IsWf.exists_fst {Γ p} (h : IsWf Γ (.fst p)) : ∃A B, HasTy Γ (.sigma A B) p
  := have ⟨_, h⟩ := h.has_ty; h.exists_fst

theorem Ctx.IsWf.exists_snd {Γ p} (h : IsWf Γ (.snd p)) : ∃A B, HasTy Γ (.sigma A B) p
  := have ⟨_, h⟩ := h.has_ty; h.exists_snd

theorem Ctx.IsWf.of_fst {Γ p} (h : IsWf Γ (.fst p)) : IsWf Γ p
  := have ⟨_, _, h⟩ := h.exists_fst; h.is_wf

theorem Ctx.IsWf.of_snd {Γ p} (h : IsWf Γ (.snd p)) : IsWf Γ p
  := have ⟨_, _, h⟩ := h.exists_snd; h.is_wf

theorem Ctx.HasTy.exists_pair_general {Γ U a b P} (h : HasTy Γ U P) (hP : P = .pair a b)
  : ∃A, ∃ B : Tm 1, IsTyUnder Γ A B ∧ HasTy Γ A a ∧ HasTy Γ (B.lst a) b := by
  induction h with
  | pair' hA hB ha hb =>
    cases hP;
    exact ⟨_, _, (fun x hx => (HasTy.top_quant_exact_k hB x hx).is_ty), ha, hb⟩
  | _ => cases hP <;> apply_assumption <;> rfl

theorem Ctx.HasTy.exists_pair {Γ U a b} (h : HasTy Γ U (.pair a b))
  : ∃A, ∃ B : Tm 1, IsTyUnder Γ A B ∧ HasTy Γ A a ∧ HasTy Γ (B.lst a) b
  := exists_pair_general h rfl

theorem Ctx.IsWf.exists_pair {Γ a b} (h : IsWf Γ (.pair a b))
  : ∃A, ∃ B : Tm 1, IsTyUnder Γ A B ∧ HasTy Γ A a ∧ HasTy Γ (B.lst a) b
  := have ⟨_, h⟩ := h.has_ty; h.exists_pair

theorem Ctx.JEq.fst {Γ} {A : Tm 0} {B : Tm 1} {p p' : Tm 0}
    (hp : JEq Γ (.sigma A B) p p')
    : JEq Γ A (p.fst) (p'.fst) :=
    have ⟨_, hA⟩ := hp.regular.wf.exists_sigma_arg;
    have ⟨_, hB⟩ := hp.regular.wf.exists_sigma_res;
    .fst' (fun x hx => (hB x hx).refl) hA.refl hp

theorem Ctx.JEq.snd {Γ} {A : Tm 0} {B : Tm 1} {p p' : Tm 0}
    (hp : JEq Γ (.sigma A B) p p')
    : JEq Γ (B.lst (p.fst)) (p.snd) (p'.snd) :=
    have ⟨_, hA⟩ := hp.regular.wf.exists_sigma_arg;
    have ⟨_, hB⟩ := hp.regular.wf.exists_sigma_res;
    .snd' (fun x hx => (hB x hx).refl) hA.refl hp
      (.lst_cf₁_k (fun x hx => (hB x hx).refl) (.fst hp.lhs_ty'))

theorem Ctx.JEq.beta_fst_both {Γ} {A : Tm 0} {B : Tm 1} {a b : Tm 0} {L : Finset String}
    (hB : ∀ x ∉ L, IsTy (Γ.cons x A) (B.open x))
    (ha : HasTy Γ A a) (hb : HasTy Γ (B.lst a) b)
    : JEq Γ A (.fst (.pair a b)) a
    :=
    have ⟨_, hA⟩ := ha.regular;
    have ⟨_, hB⟩ := IsTy.max_univ' hB;
    have hpair := (JEq.pair' hB hA ha.refl hb.refl)
    .beta_fst' hA hB hpair (.fst hpair) ha.refl

theorem Ctx.JEq.beta_snd_both {Γ} {A : Tm 0} {B : Tm 1} {a b : Tm 0} {L : Finset String}
    (hB : ∀ x ∉ L, IsTy (Γ.cons x A) (B.open x))
    (ha : HasTy Γ A a) (hb : HasTy Γ (B.lst a) b)
    : JEq Γ (B.lst a) (.snd (.pair a b)) b
    :=
    have ⟨_, hA⟩ := ha.regular;
    have ⟨_, hB'⟩ := IsTy.max_univ' hB;
    have hfst := JEq.beta_fst_both hB ha hb
    have hpair := (JEq.pair' hB' hA ha.refl hb.refl)
    (JEq.beta_snd' hA hB' hpair (.snd hpair) (hb.lst_cast hB' hfst.symm).refl).cast
      (TyEq.lst_cf hB hfst)
