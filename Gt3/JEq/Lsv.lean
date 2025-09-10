import Gt3.JEq.Regular

theorem Ctx.SEq.lset_cons {Γ x A a b} (hx : x ∉ Γ.dv) (hab : JEq Γ A a b)
  : SEq Γ (.lset a x) (.lset b x) (Γ.cons x A) := by
  have hA := hab.regular
  have hA' := Tm.ls_lset_not_mem (hx := Finset.not_mem_subset hA.scoped hx)
  have ha := Tm.ls_lset_not_mem (hx := Finset.not_mem_subset hab.lhs_scoped hx)
  have hb := Tm.ls_lset_not_mem (hx := Finset.not_mem_subset hab.rhs_scoped hx)
  apply (SEq.lset hab.ok hx hx a b).cons' <;> simp [*]

theorem Ctx.JEq.lsv₁ {Γ : Ctx} {A B a b b' : Tm 0} {x : String}
  (hb : Ctx.JEq (Γ.cons x A) B b b') (ha : Ctx.JEq Γ A a a)
  : Γ.JEq (B.lsv x a) (b.lsv x a) (b'.lsv x a)
  := by
  convert hb.ls1' (.lset_cons hb.ok.var ha) using 1 <;> simp [Tm.ls_lset]

theorem Ctx.JEq.lst₁ {Γ : Ctx} {A a : Tm 0} {B b b' : Tm 1} {x : String}
  (hx : x ∉ B.fvs ∪ b.fvs ∪ b'.fvs)
  (hb : Ctx.JEq (Γ.cons x A) (B.open x) (b.open x) (b'.open x))
  (ha : Ctx.JEq Γ A a a) : Γ.JEq (B.lst a) (b.lst a) (b'.lst a) := by
  simp at hx
  convert hb.lsv₁ ha using 1 <;> rw [Tm.lsv_open] <;> simp [*]

theorem Ctx.JEq.lst_cf₁ {Γ : Ctx} {A a : Tm 0} {B b b' : Tm 1} {L : Finset String}
  (hb : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (B.open x) (b.open x) (b'.open x))
  (ha : Ctx.JEq Γ A a a) : Γ.JEq (B.lst a) (b.lst a) (b'.lst a) := by
  have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ (B.fvs ∪ b.fvs ∪ b'.fvs))
  rw [Finset.notMem_union] at hx
  exact (hb x hx.1).lst₁ hx.2 ha

theorem Ctx.JEq.lst₁_k {Γ : Ctx} {A a B : Tm 0} {b b' : Tm 1} {x : String}
  (hx : x ∉ B.fvs ∪ b.fvs ∪ b'.fvs)
  (hb : Ctx.JEq (Γ.cons x A) B (b.open x) (b'.open x))
  (ha : Ctx.JEq Γ A a a) : Γ.JEq B (b.lst a) (b'.lst a) := by
  simp only [Finset.notMem_union] at hx
  convert hb.lsv₁ ha using 1
  · rw [Tm.lsv_not_mem (hx := by simp [*])]
  · rw [Tm.lsv_open (hx := by simp [*])]
  · rw [Tm.lsv_open (hx := by simp [*])]

theorem Ctx.JEq.lst_cf₁_k {Γ : Ctx} {A a B : Tm 0} {b b' : Tm 1} {L : Finset String}
  (hb : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) B (b.open x) (b'.open x))
  (ha : Ctx.JEq Γ A a a) : Γ.JEq B (b.lst a) (b'.lst a) := by
  have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ (B.fvs ∪ b.fvs ∪ b'.fvs))
  rw [Finset.notMem_union] at hx
  exact (hb x hx.1).lst₁_k hx.2 ha

theorem Ctx.TyEq.lst₁ {Γ : Ctx} {A a : Tm 0} {B B' : Tm 1} {x : String} (hx : x ∉ B.fvs ∪ B'.fvs)
  (hb : Ctx.TyEq (Γ.cons x A) (B.open x) (B'.open x))
  (ha : Ctx.JEq Γ A a a) : Γ.TyEq (B.lst a) (B'.lst a)
  := have ⟨ℓ, hb⟩ := hb; ⟨ℓ, hb.lst₁_k (by simp [hx]) ha⟩

theorem Ctx.JEq.lst_cf_univ {Γ : Ctx} {n : ℕ} {A a a'} {B B' : Tm 1} {L : Finset String}
  (hB : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
  (ha : Ctx.JEq Γ A a a') : JEq Γ (.univ n) (B.lst a) (B'.lst a') :=
  have ⟨m, hA⟩ := ha.regular;
  have hAB : Ctx.JEq Γ (.pi A (.univ n)) (.abs A (.univ n) B) (.abs A (.univ n) B') :=
    .abs hA
      (fun x hx => by convert JEq.univ (hB x hx).ok using 0; rw[Tm.open_univ])
      (fun x hx => by convert hB x hx using 0 ; rw [Tm.open_univ])
  have app_eq
    : Ctx.JEq Γ (.univ n) (.app (.abs A (.univ n) B) a) (.app (.abs A (.univ n) B') a')
    := .app hAB ha (by simp [hA.ok])
  have hba : Ctx.JEq Γ (.univ n) (.app (.abs A (.univ n) B) a) (B.lst a)
    := .beta_app hAB.lhs_ty' ha.lhs_ty' (.lst_cf₁_k (fun x hx => (hB x hx).lhs_ty') ha.lhs_ty')
  have hba' : Ctx.JEq Γ (.univ n) (.app (.abs A (.univ n) B') a') (B'.lst a')
    := .beta_app hAB.rhs_ty' ha.rhs_ty' (.lst_cf₁_k (fun x hx => (hB x hx).rhs_ty') ha.rhs_ty')
  hba.symm.trans (app_eq.trans hba')

theorem Ctx.TyEq.lst_cf {Γ : Ctx} {A a a'} {B B' : Tm 1} {L : Finset String}
  (hB : ∀ x ∉ L, Ctx.TyEq (Γ.cons x A) (B.open x) (B'.open x))
  (ha : Ctx.JEq Γ A a a') : TyEq Γ (B.lst a) (B'.lst a')
  := have ⟨ℓ, hB⟩ := TyEq.max_univ' hB; ⟨ℓ, JEq.lst_cf_univ hB ha⟩

theorem Ctx.IsTy.lst_cf' {Γ : Ctx} {A a a'} {B : Tm 1} {L : Finset String}
  (hB : ∀ x ∉ L, Ctx.IsTy (Γ.cons x A) (B.open x))
  (ha : Ctx.JEq Γ A a a') : IsTy Γ (B.lst a)
  := TyEq.lst_cf hB ha.lhs_ty'

theorem Ctx.TyEq.lst_cf_k' {Γ : Ctx} {A a a' B B'} {L : Finset String}
  (hB : ∀ x ∉ L, Ctx.TyEq (Γ.cons x A) B B')
  (ha : Ctx.JEq Γ A a a') : TyEq Γ B B'
  := by
  rw [<-B.lst_castSucc a, <-B'.lst_castSucc a']
  apply lst_cf (L := L) _ ha
  convert hB <;> simp

theorem Ctx.IsTy.lst_cf_k' {Γ : Ctx} {A a a' B} {L : Finset String}
  (hB : ∀ x ∉ L, Ctx.IsTy (Γ.cons x A) B)
  (ha : Ctx.JEq Γ A a a') : IsTy Γ B
  := TyEq.lst_cf_k' hB ha

theorem Ctx.JEq.lst_cf {Γ : Ctx} {A a a'} {B b b' : Tm 1} {L : Finset String}
  (hb : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (B.open x) (b.open x) (b'.open x))
  (ha : Ctx.JEq Γ A a a') : Γ.JEq (B.lst a) (b.lst a) (b'.lst a') := by
  have ⟨m, hA⟩ := ha.regular;
  have ⟨n, hB⟩ := IsTy.max_univ' (fun x hx => (hb x hx).regular)
  have hB' := JEq.lst_cf_univ hB ha
  have hB : ∀x ∉ L ∪ Γ.dv, Ctx.JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x)
    := fun x hx => by simp at hx; exact hB x hx.left
  have hb : ∀x ∉ L ∪ Γ.dv, Ctx.JEq (Γ.cons x A) (B.open x) (b.open x) (b'.open x)
    := fun x hx => by simp at hx; exact hb x hx.left
  have app_eq
    : Ctx.JEq Γ (B.lst a) (.app (.abs A B b) a) (.app (.abs A B b') a')
    := .app (.abs hA hB hb) ha hB'.lhs_is_ty
  have hbl := (fun x hx => (hb x hx).lhs_ty')
  have hba : Ctx.JEq Γ (B.lst a) (.app (.abs A B b) a) (b.lst a)
    := .beta_app (.abs hA hB hbl) ha.lhs_ty' (.lst_cf₁ hbl ha.lhs_ty')
  have hbr := (fun x hx => (hb x hx).rhs_ty')
  have hba' : Ctx.JEq Γ (B.lst a') (.app (.abs A B b') a') (b'.lst a')
    :=.beta_app (.abs hA hB hbr) ha.rhs_ty' (.lst_cf₁ hbr ha.rhs_ty')
  exact hba.symm.trans (app_eq.trans (hB'.symm.cast' hba'))
