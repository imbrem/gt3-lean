import Gt3.Universe.Subst
import Gt3.Syntax.Erase
import Gt3.Ctx

namespace Gt3

@[simp]
def Tm.uvs {k} : Tm k → Finset String
  | .univ ℓ => ℓ.uvs
  | .eqn a b => a.uvs ∪ b.uvs
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
  | .succ n => n.uvs
  | .natrec C s z n => (C.uvs) ∪ (s.uvs) ∪ (z.uvs) ∪ (n.uvs)
  | .has_ty A a => (A.uvs) ∪ (a.uvs)
  | _ => ∅

@[simp]
def Tm.us (σ : ULevel.Subst) {k} : Tm k → Tm k
  | .univ ℓ => .univ (ℓ.subst σ)
  | .eqn a b => .eqn (a.us σ) (b.us σ)
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
  | .succ n => .succ (n.us σ)
  | .natrec C s z n => .natrec (C.us σ) (s.us σ) (z.us σ) (n.us σ)
  | .has_ty A a => .has_ty (A.us σ) (a.us σ)
  | t => t

@[simp]
def OTm.uvs : OTm → Finset String
  | .univ ℓ => ℓ.uvs
  | .eqn a b => a.uvs ∪ b.uvs
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
  | .succ n => n.uvs
  | .natrec C s z n => (C.uvs) ∪ (s.uvs) ∪ (z.uvs) ∪ (n.uvs)
  | .has_ty A a => (A.uvs) ∪ (a.uvs)
  | _ => ∅

@[simp]
def OTm.us (σ : ULevel.Subst) : OTm → OTm
  | .univ ℓ => .univ (ℓ.subst σ)
  | .eqn a b => .eqn (a.us σ) (b.us σ)
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
  | .succ n => .succ (n.us σ)
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
theorem Tm.us_erase {k} (σ : ULevel.Subst) (t : Tm k) : t.erase.us σ = (t.us σ).erase
  := by induction t <;> simp [erase, *]

@[simp]
theorem OTm.us_clamp (σ : ULevel.Subst) (t : OTm) (k) : (t.clamp k).us σ = (t.us σ).clamp k
  := by induction t generalizing k with
  | bv => simp [clamp]; split <;> rfl
  | _ => simp [clamp, *]

def Ctx.uvs : Ctx → Finset String
  | .nil => ∅
  | .cons Γ _ A => (Γ.uvs) ∪ (A.uvs)

@[simp]
def Ctx.us (σ : ULevel.Subst) : Ctx → Ctx
  | .nil => .nil
  | .cons Γ x A => .cons (Γ.us σ) x (A.us σ)

@[simp]
theorem Tm.fvs_us {σ : ULevel.Subst} {k} (t : Tm k) : (t.us σ).fvs = t.fvs := by
  induction t <;> simp [*]

@[simp]
theorem Ctx.dv_us {σ : ULevel.Subst} {Γ : Ctx} : (Γ.us σ).dv = Γ.dv := by induction Γ <;> simp [*]

theorem Ctx.Lookup.us {σ : ULevel.Subst} {Γ : Ctx} {x : String} {A : Tm 0}
  (h : Ctx.Lookup Γ x A) : Ctx.Lookup (Γ.us σ) x (A.us σ) := by induction h with
  | here hΓ => simp
  | there hΓ hA => apply Ctx.Lookup.there <;> assumption

theorem OTm.us_eqOn_subset {us : Finset String} {σ σ' : ULevel.Subst}
  (hσ : σ.EqOn us σ') (t : OTm) (h : t.uvs ⊆ us) :
  t.us σ = t.us σ' := by induction t with
  | univ => simp; apply ULevel.subst_eqOn_subset <;> assumption
  | _ => simp [Finset.union_subset_iff] at * <;> simp [*]

theorem OTm.us_eqOn {σ σ' : ULevel.Subst} (t : OTm) (hσ : σ.EqOn t.uvs σ') :
  t.us σ = t.us σ' := us_eqOn_subset hσ t (by simp)

theorem Tm.us_eqOn_subset {k} {us : Finset String} {σ σ' : ULevel.Subst}
  (hσ : σ.EqOn us σ') (t : Tm k) (h : t.uvs ⊆ us) :
  t.us σ = t.us σ' := by
  apply Tm.erase_injective
  rw [<-Tm.us_erase, <-Tm.us_erase]
  exact OTm.us_eqOn_subset hσ _ (Tm.uvs_erase t ▸ h)

theorem Tm.us_eqOn {k} {σ σ' : ULevel.Subst} (t : Tm k) (hσ : σ.EqOn t.uvs σ') :
  t.us σ = t.us σ' := us_eqOn_subset hσ t (by simp)

@[simp]
theorem OTm.us_one (t : OTm) : t.us 1 = t := by induction t <;> simp [*]

@[simp]
theorem Tm.us_one {k} (t : Tm k) : t.us 1 = t := by apply Tm.erase_injective; simp [<-Tm.us_erase]

theorem OTm.us_one_subset {us : Finset String} {σ : ULevel.Subst}
  (hσ : σ.EqOn us 1) (t : OTm) (h : t.uvs ⊆ us) :
  t.us σ = t := by convert OTm.us_eqOn_subset hσ t h; simp

theorem Tm.us_one_subset {k} {us : Finset String} {σ : ULevel.Subst}
  (hσ : σ.EqOn us 1) (t : Tm k) (h : t.uvs ⊆ us) :
  t.us σ = t := by convert Tm.us_eqOn_subset hσ t h; simp

theorem OTm.us_one_eqOn {σ : ULevel.Subst} (t : OTm) (hσ : σ.EqOn t.uvs 1) :
  t.us σ = t := us_one_subset hσ t (by simp)

theorem Tm.us_one_eqOn {σ : ULevel.Subst} {k} (t : Tm k) (hσ : σ.EqOn t.uvs 1) :
  t.us σ = t := us_one_subset hσ t (by simp)

@[simp]
theorem OTm.us_lst (σ t k a) :
  (OTm.lst t k a).us σ = (t.us σ).lst k (a.us σ) := by induction t generalizing k with
  | bv => simp; split_ifs <;> rfl
  | _ => simp [*]

@[simp]
theorem Tm.us_lst {k} (σ : ULevel.Subst) (t : Tm (k + 1)) (a : Tm 0) :
  (t.lst a).us σ = (t.us σ).lst (a.us σ) := by
  apply Tm.erase_injective
  simp [Tm.erase_lst, <-Tm.us_erase]

@[simp]
theorem OTm.us_open (σ t k x) :
  (OTm.open k x t).us σ = (t.us σ).open k x := by simp only [<-OTm.lst_of_fv]; simp

@[simp]
theorem Tm.us_open {k} (σ : ULevel.Subst) (t : Tm (k + 1)) (x : String) :
  (t.open x).us σ = (t.us σ).open x := by
  apply Tm.erase_injective
  simp [Tm.erase_open, <-Tm.us_erase]

@[simp]
theorem Tm.us_wkn {k} (σ : ULevel.Subst) (t : Tm k) (n) :
  (t.wkn n).us σ = (t.us σ).wkn (n) := by induction t generalizing n with
  | bv => simp [wkn]; split_ifs <;> rfl
  | _ => simp [wkn, *]

@[simp]
theorem Tm.us_wk0 {k} (σ : ULevel.Subst) (t : Tm k) :
  (t.wk0).us σ = (t.us σ).wk0 := by simp [Tm.wk0]

@[simp]
theorem Tm.us_arr {k} (σ : ULevel.Subst) (A B : Tm k) :
  (A.arr B).us σ = (A.us σ).arr (B.us σ) := by simp [Tm.arr]

@[simp]
theorem Tm.us_st {k} (σ : ULevel.Subst) (t : Tm (k + 1)) (v : Tm k) :
  (t.st v).us σ = (t.us σ).st (v.us σ) := by induction t using succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp
  | _ => simp [st, *]

@[simp]
theorem Tm.us_sth {k} (σ : ULevel.Subst) (t : Tm (k + 1)) (v : Tm (k + 1)) :
  (t.sth v).us σ = (t.us σ).sth (v.us σ) := by simp [Tm.sth]

@[simp]
theorem Tm.us_succIn {k} (σ : ULevel.Subst) (C : Tm (k + 1)) :
  (Tm.succIn C).us σ = Tm.succIn (C.us σ) := by simp [Tm.succIn]

@[simp]
theorem Tm.us_succArrow {k} (σ : ULevel.Subst) (C : Tm (k + 1)) :
  (Tm.succArrow C).us σ = Tm.succArrow (C.us σ) := by simp [Tm.succArrow]

end Gt3
