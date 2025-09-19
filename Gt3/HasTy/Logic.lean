import Gt3.HasTy.Regular

def Ctx.PropEq (Γ φ ψ) := JEq Γ (.univ 0) φ ψ

theorem Ctx.PropEq.symm {Γ φ ψ} (h : PropEq Γ φ ψ) : PropEq Γ ψ φ := JEq.symm h

theorem Ctx.PropEq.trans {Γ φ ψ θ}
  (hφψ : PropEq Γ φ ψ) (hψθ : PropEq Γ ψ θ) : PropEq Γ φ θ := JEq.trans hφψ hψθ

def Ctx.IsProp (Γ φ) := HasTy Γ (.univ 0) φ

theorem Ctx.IsProp.refl {Γ φ} (h : IsProp Γ φ) : PropEq Γ φ φ := HasTy.refl h

theorem Ctx.PropEq.lhs {Γ φ ψ} (h : PropEq Γ φ ψ) : IsProp Γ φ := JEq.lhs_ty h

theorem Ctx.PropEq.rhs {Γ φ ψ} (h : PropEq Γ φ ψ) : IsProp Γ ψ := JEq.rhs_ty h

theorem Ctx.PropEq.refl_iff {Γ φ} : PropEq Γ φ φ ↔ IsProp Γ φ := ⟨lhs, IsProp.refl⟩

def Ctx.IsTrue (Γ φ) := PropEq Γ φ .unit

def Ctx.IsFalse (Γ φ) := PropEq Γ φ .empty

theorem Ctx.IsTrue.is_prop {Γ φ} (h : IsTrue Γ φ) : IsProp Γ φ := PropEq.lhs h

theorem Ctx.IsFalse.is_prop {Γ φ} (h : IsFalse Γ φ) : IsProp Γ φ := PropEq.lhs h

theorem Ctx.PropEq.tt_mp {Γ φ ψ} (h : PropEq Γ φ ψ) (hφ : IsTrue Γ φ) : IsTrue Γ ψ
  := PropEq.trans h.symm hφ

theorem Ctx.PropEq.tt_iff {Γ φ ψ} (h : PropEq Γ φ ψ) : IsTrue Γ φ ↔ IsTrue Γ ψ
  := ⟨h.tt_mp, h.symm.tt_mp⟩

theorem Ctx.JEq.ite_k_tt {Γ A l r}
  (hl : JEq Γ A l l)
  (hr : JEq Γ A r r)
  : JEq Γ A (.ite .unit l r) l :=
  have ⟨ℓ, hA⟩ := hl.regular;
  JEq.beta_dite_tt' (l := ↑₀ l) (r := ↑₀ r) (lu := l) (L := Γ.dv)
      hA (fun x hx => by convert hl.wk0 hx (.unit hl.ok) <;> simp)
      (.ite_k (.unit hl.ok) hl hr) (by convert hl <;> simp) (by convert hl; simp)

theorem Ctx.JEq.ite_k_ff {Γ A l r}
  (hl : JEq Γ A l l)
  (hr : JEq Γ A r r)
  : JEq Γ A (.ite .empty l r) r :=
  have ⟨ℓ, hA⟩ := hl.regular;
  JEq.beta_dite_ff' (l := ↑₀ l) (r := ↑₀ r) (ru := r) (L := Γ.dv)
      hA (fun x hx => by convert hr.wk0 hx (.not (.empty hl.ok)) <;> simp)
      (.ite_k (.empty hl.ok) hl hr) (by convert hr <;> simp) (by convert hr; simp)

theorem Ctx.JEq.ite_k_ett {Γ A φ l r}
  (hφ : JEq Γ (.univ 0) φ .unit)
  (hl : JEq Γ A l l)
  (hr : JEq Γ A r r)
  : JEq Γ A (.ite φ l r) l := .trans (.ite_k hφ hl hr) (.ite_k_tt hl hr)

theorem Ctx.JEq.ite_k_eff {Γ A φ l r}
  (hφ : JEq Γ (.univ 0) φ .empty)
  (hl : JEq Γ A l l)
  (hr : JEq Γ A r r)
  : JEq Γ A (.ite φ l r) r := .trans (.ite_k hφ hl hr) (.ite_k_ff hl hr)
