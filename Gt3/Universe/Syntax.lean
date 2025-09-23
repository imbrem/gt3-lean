import Gt3.Universe.Subst
import Gt3.Syntax.Erase
import Gt3.Ctx

@[simp]
def Tm.uvs {k} : Tm k → Finset String
  | .univ ℓ => ℓ.uvs
  | .pi A B => (A.uvs) ∪ (B.uvs)
  | .sigma A B => (A.uvs) ∪ (B.uvs)
  | .abs A b => A.uvs ∪ b.uvs
  | .app f a => f.uvs ∪ a.uvs
  | .pair a b => a.uvs ∪ b.uvs
  | .fst p => p.uvs
  | .snd p => p.uvs
  | .dite φ l r => (φ.uvs) ∪ (l.uvs) ∪ (r.uvs)
  | .trunc A => A.uvs
  | .choose A φ => (A.uvs) ∪ (φ.uvs)
  | .natrec C s z n => (C.uvs) ∪ (s.uvs) ∪ (z.uvs) ∪ (n.uvs)
  | .has_ty A a => (A.uvs) ∪ (a.uvs)
  | _ => ∅

@[simp]
def Tm.us (σ : ULevel.Subst) {k} : Tm k → Tm k
  | .univ ℓ => .univ (ℓ.subst σ)
  | .pi A B => .pi (A.us σ) (B.us σ)
  | .sigma A B => .sigma (A.us σ) (B.us σ)
  | .abs A b => .abs (A.us σ) (b.us σ)
  | .app f a => .app (f.us σ) (a.us σ)
  | .pair a b => .pair (a.us σ) (b.us σ)
  | .fst p => .fst (p.us σ)
  | .snd p => .snd (p.us σ)
  | .dite φ l r => .dite (φ.us σ) (l.us σ) (r.us σ)
  | .trunc A => .trunc (A.us σ)
  | .choose A φ => .choose (A.us σ) (φ.us σ)
  | .natrec C s z n => .natrec (C.us σ) (s.us σ) (z.us σ) (n.us σ)
  | .has_ty A a => .has_ty (A.us σ) (a.us σ)
  | t => t

@[simp]
def OTm.uvs : OTm → Finset String
  | .univ ℓ => ℓ.uvs
  | .pi A B => (A.uvs) ∪ (B.uvs)
  | .sigma A B => (A.uvs) ∪ (B.uvs)
  | .abs A b => A.uvs ∪ b.uvs
  | .app f a => f.uvs ∪ a.uvs
  | .pair a b => a.uvs ∪ b.uvs
  | .fst p => p.uvs
  | .snd p => p.uvs
  | .dite φ l r => (φ.uvs) ∪ (l.uvs) ∪ (r.uvs)
  | .trunc A => A.uvs
  | .choose A φ => (A.uvs) ∪ (φ.uvs)
  | .natrec C s z n => (C.uvs) ∪ (s.uvs) ∪ (z.uvs) ∪ (n.uvs)
  | .has_ty A a => (A.uvs) ∪ (a.uvs)
  | _ => ∅

@[simp]
def OTm.us (σ : ULevel.Subst) : OTm → OTm
  | .univ ℓ => .univ (ℓ.subst σ)
  | .pi A B => .pi (A.us σ) (B.us σ)
  | .sigma A B => .sigma (A.us σ) (B.us σ)
  | .abs A b => .abs (A.us σ) (b.us σ)
  | .app f a => .app (f.us σ) (a.us σ)
  | .pair a b => .pair (a.us σ) (b.us σ)
  | .fst p => .fst (p.us σ)
  | .snd p => .snd (p.us σ)
  | .dite φ l r => .dite (φ.us σ) (l.us σ) (r.us σ)
  | .trunc A => .trunc (A.us σ)
  | .choose A φ => .choose (A.us σ) (φ.us σ)
  | .natrec C s z n => .natrec (C.us σ) (s.us σ) (z.us σ) (n.us σ)
  | .has_ty A a => .has_ty (A.us σ) (a.us σ)
  | t => t

@[simp]
theorem Tm.uvs_erase {k} (t : Tm k) : (t.erase).uvs = t.uvs := by induction t <;> simp [erase, *]

@[simp]
theorem OTm.uvs_clamp (t : OTm) (k) : (t.clamp k).uvs = t.uvs
  := by induction t generalizing k with
  | bv => simp only [clamp]; split <;> rfl
  | _ => simp [clamp, *]

@[simp]
theorem Tm.us_erase {k} (σ : ULevel.Subst) (t : Tm k) : (t.us σ).erase = t.erase.us σ
  := by induction t <;> simp [erase, *]

@[simp]
theorem OTm.us_clamp (σ : ULevel.Subst) (t : OTm) (k) : (t.us σ).clamp k = (t.clamp k).us σ
  := by induction t generalizing k with
  | bv => simp [clamp]; split <;> rfl
  | _ => simp [clamp, *]

def Ctx.uvs : Ctx → Finset String
  | .nil => ∅
  | .cons Γ _ A => (Γ.uvs) ∪ (A.uvs)

def Ctx.us (σ : ULevel.Subst) : Ctx → Ctx
  | .nil => .nil
  | .cons Γ x A => .cons (Γ.us σ) x (A.us σ)

theorem OTm.subst_eqOn_subset {us : Finset String} {σ σ' : ULevel.Subst}
  (hσ : σ.EqOn us σ') (t : OTm) (h : t.uvs ⊆ us) :
  t.us σ = t.us σ' := by induction t with
  | univ => simp; apply ULevel.subst_eqOn_subset <;> assumption
  | _ => simp [Finset.union_subset_iff] at * <;> simp [*]

theorem OTm.subst_eqOn {σ σ' : ULevel.Subst} (t : OTm) (hσ : σ.EqOn t.uvs σ') :
  t.us σ = t.us σ' := subst_eqOn_subset hσ t (by simp)

theorem Tm.subst_eqOn_subset {k} {us : Finset String} {σ σ' : ULevel.Subst}
  (hσ : σ.EqOn us σ') (t : Tm k) (h : t.uvs ⊆ us) :
  t.us σ = t.us σ' := by
  apply Tm.erase_injective
  rw [Tm.us_erase, Tm.us_erase]
  exact OTm.subst_eqOn_subset hσ _ (Tm.uvs_erase t ▸ h)

theorem Tm.subst_eqOn {k} {σ σ' : ULevel.Subst} (t : Tm k) (hσ : σ.EqOn t.uvs σ') :
  t.us σ = t.us σ' := subst_eqOn_subset hσ t (by simp)

@[simp]
theorem OTm.subst_one (t : OTm) : t.us 1 = t := by induction t <;> simp [*]

@[simp]
theorem Tm.subst_one {k} (t : Tm k) : t.us 1 = t := by apply Tm.erase_injective; simp

theorem OTm.subst_one_subset {us : Finset String} {σ : ULevel.Subst}
  (hσ : σ.EqOn us 1) (t : OTm) (h : t.uvs ⊆ us) :
  t.us σ = t := by convert OTm.subst_eqOn_subset hσ t h; simp

theorem Tm.subst_one_subset {k} {us : Finset String} {σ : ULevel.Subst}
  (hσ : σ.EqOn us 1) (t : Tm k) (h : t.uvs ⊆ us) :
  t.us σ = t := by convert Tm.subst_eqOn_subset hσ t h; simp

theorem OTm.subst_one_eqOn {σ : ULevel.Subst} (t : OTm) (hσ : σ.EqOn t.uvs 1) :
  t.us σ = t := subst_one_subset hσ t (by simp)

theorem Tm.subst_one_eqOn {σ : ULevel.Subst} {k} (t : Tm k) (hσ : σ.EqOn t.uvs 1) :
  t.us σ = t := subst_one_subset hσ t (by simp)
