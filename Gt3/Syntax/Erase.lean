import Gt3.Syntax.Basic

inductive OTm : Type
  | fv (x : String) : OTm
  | bv (i : ℕ) : OTm
  | univ (ℓ : ℕ) : OTm
  | empty : OTm
  | unit : OTm
  | null : OTm
  | eqn (a b : OTm) : OTm
  | pi (A B : OTm) : OTm
  | sigma (A B : OTm) : OTm
  | abs (A : OTm) (b : OTm) : OTm
  | app (f a : OTm) : OTm
  | pair (a b : OTm) : OTm
  | fst (p : OTm) : OTm
  | snd (p : OTm) : OTm
  | dite (φ l r : OTm) : OTm
  | trunc (A : OTm) : OTm
  | choose (A φ : OTm) : OTm
  | nats : OTm
  | zero : OTm
  | succ (n : OTm) : OTm
  | natrec (C s z n : OTm) : OTm
  | has_ty (A a : OTm) : OTm
  | invalid : OTm

def Tm.erase {k : ℕ} : Tm k → OTm
  | .fv x => .fv x
  | .bv i => .bv i
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn a.erase b.erase
  | .pi A B => .pi A.erase B.erase
  | .sigma A B => .sigma A.erase B.erase
  | .abs A b => .abs A.erase b.erase
  | .app f a => .app f.erase a.erase
  | .pair a b => .pair a.erase b.erase
  | .fst p => .fst p.erase
  | .snd p => .snd p.erase
  | .dite φ l r => .dite φ.erase l.erase r.erase
  | .trunc A => .trunc A.erase
  | .choose A φ => .choose A.erase φ.erase
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ n.erase
  | .natrec C s z n => .natrec C.erase s.erase z.erase n.erase
  | .has_ty A a => .has_ty A.erase a.erase
  | .invalid => .invalid

def OTm.clamp (k : ℕ) : OTm → Tm k
  | .fv x => .fv x
  | .bv i => if h : i < k then .bv ⟨i, h⟩ else .invalid
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.clamp k) (b.clamp k)
  | .pi A B => .pi (A.clamp k) (B.clamp (k + 1))
  | .sigma A B => .sigma (A.clamp k) (B.clamp (k + 1))
  | .abs A b => .abs (A.clamp k) (b.clamp (k + 1))
  | .app f a => .app (f.clamp k) (a.clamp k)
  | .pair a b => .pair (a.clamp k) (b.clamp k)
  | .fst p => .fst (p.clamp k)
  | .snd p => .snd (p.clamp k)
  | .dite φ l r => .dite (φ.clamp k) (l.clamp (k + 1)) (r.clamp (k + 1))
  | .trunc A => .trunc (A.clamp k)
  | .choose A φ => .choose (A.clamp k) (φ.clamp (k + 1))
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.clamp k)
  | .natrec C s z n => .natrec (C.clamp (k + 1)) (s.clamp (k + 1)) (z.clamp k) (n.clamp k)
  | .has_ty A a => .has_ty (A.clamp k) (a.clamp k)
  | .invalid => .invalid

@[simp]
theorem Tm.clamp_erase {k : ℕ} (t : Tm k) : t.erase.clamp k = t
  := by induction t <;> simp [OTm.clamp, erase, *]

instance Tm.erase_leftInverse {k : ℕ} : Function.HasLeftInverse (Tm.erase (k := k))
  := ⟨OTm.clamp k, fun t => t.clamp_erase⟩

instance Tm.erase_injective {k : ℕ} : Function.Injective (Tm.erase (k := k))
  := erase_leftInverse.injective

@[simp]
theorem Tm.erase_castLE {n m : ℕ} (h : n ≤ m) (t : Tm n) : (t.castLE h).erase = t.erase
  := by induction t generalizing m <;> simp [erase, castLE, *]

@[simp]
theorem Tm.erase_castAdd {k : ℕ} (t : Tm k) (n : ℕ) : (t.castAdd n).erase = t.erase
  := t.erase_castLE _

@[simp]
theorem Tm.erase_castSucc {k : ℕ} (t : Tm k) : t.castSucc.erase = t.erase
  := t.erase_castLE _

def OTm.fvs : OTm → Finset String
  | .fv x => {x}
  | .eqn a b => a.fvs ∪ b.fvs
  | .pi A B => A.fvs ∪ B.fvs
  | .sigma A B => A.fvs ∪ B.fvs
  | .abs A b => A.fvs ∪ b.fvs
  | .app f a => f.fvs ∪ a.fvs
  | .pair a b => a.fvs ∪ b.fvs
  | .fst p => p.fvs
  | .snd p => p.fvs
  | .dite φ l r => φ.fvs ∪ l.fvs ∪ r.fvs
  | .trunc A => A.fvs
  | .choose A φ => A.fvs ∪ φ.fvs
  | .succ n => n.fvs
  | .natrec C s z n => C.fvs ∪ s.fvs ∪ z.fvs ∪ n.fvs
  | .has_ty A a => A.fvs ∪ a.fvs
  | _ => ∅

@[simp]
theorem Tm.fvs_erase {k : ℕ} (t : Tm k) : t.erase.fvs = t.fvs
  := by induction t <;> simp [erase, fvs, OTm.fvs, *]

@[simp]
theorem OTm.fvs_clamp (k : ℕ) (t : OTm) : (t.clamp k).fvs = t.fvs
  := by induction t generalizing k with
  | bv i => simp only [clamp]; split <;> rfl
  | _ => simp [clamp, fvs, Tm.fvs, *]

def Tm.bvi {k : ℕ} : Tm k → ℕ
  | .bv i => i + 1
  | .eqn a b => a.bvi ⊔ b.bvi
  | .pi A B => A.bvi ⊔ (B.bvi - 1)
  | .sigma A B => A.bvi ⊔ (B.bvi - 1)
  | .abs A b => A.bvi ⊔ (b.bvi - 1)
  | .app f a => f.bvi ⊔ a.bvi
  | .pair a b => a.bvi ⊔ b.bvi
  | .fst p => p.bvi
  | .snd p => p.bvi
  | .dite φ l r => φ.bvi ⊔ (l.bvi - 1) ⊔ (r.bvi - 1)
  | .trunc A => A.bvi
  | .choose A φ => A.bvi ⊔ (φ.bvi - 1)
  | .succ n => n.bvi
  | .natrec C s z n => (C.bvi - 1) ⊔ (s.bvi - 1) ⊔ z.bvi ⊔ n.bvi
  | .has_ty A a => A.bvi ⊔ a.bvi
  | _ => 0

def OTm.bvi : OTm → ℕ
  | .bv i => i + 1
  | .eqn a b => a.bvi ⊔ b.bvi
  | .pi A B => A.bvi ⊔ (B.bvi - 1)
  | .sigma A B => A.bvi ⊔ (B.bvi - 1)
  | .abs A b => A.bvi ⊔ (b.bvi - 1)
  | .app f a => f.bvi ⊔ a.bvi
  | .pair a b => a.bvi ⊔ b.bvi
  | .fst p => p.bvi
  | .snd p => p.bvi
  | .dite φ l r => φ.bvi ⊔ (l.bvi - 1) ⊔ (r.bvi - 1)
  | .trunc A => A.bvi
  | .choose A φ => A.bvi ⊔ (φ.bvi - 1)
  | .succ n => n.bvi
  | .natrec C s z n => (C.bvi - 1) ⊔ (s.bvi - 1) ⊔ z.bvi ⊔ n.bvi
  | .has_ty A a => A.bvi ⊔ a.bvi
  | _ => 0

theorem Tm.bvi_le {k : ℕ} (t : Tm k) : t.bvi ≤ k
  := by induction t <;> simp only [bvi, sup_le_iff] <;> omega

@[simp]
theorem Tm.bvi_erase {k : ℕ} (t : Tm k) : t.erase.bvi = t.bvi
  := by induction t <;> simp [bvi, erase, OTm.bvi, *]

theorem Tm.lst_bvi_le {k : ℕ} (t : Tm (k + 1)) (v : Tm 0) : (t.lst v).bvi ≤ t.bvi := by
  induction t using succIndOn with
  | bv i =>
    cases i using Fin.lastCases <;> simp [Tm.lst, Tm.bvi]
    apply Nat.le_succ_of_le
    apply Tm.bvi_le
  | _ => simp only [Tm.lst, Tm.bvi]; omega

theorem OTm.clamp_bvi_le_clamp (k : ℕ) (t : OTm) : (t.clamp k).bvi ≤ k
  := by induction t generalizing k with
  | bv => simp only [clamp]; split <;> simp only [Tm.bvi] <;> omega
  | _ => simp [clamp, Tm.bvi, *]

theorem OTm.clamp_bvi_le_bvi (k : ℕ) (t : OTm) : (t.clamp k).bvi ≤ t.bvi
  := by induction t generalizing k with
  | bv => simp only [clamp]; split <;> simp only [Tm.bvi, bvi] <;> omega
  | _ =>
    simp only [clamp, Tm.bvi, bvi, le_refl, max_le_iff, *] <;>
    simp only [
      le_max_iff, Nat.sub_le_iff_le_add, Nat.sub_add_eq_max, true_or, true_and, *
    ] <;>
    simp

theorem OTm.erase_clamp_bvi_le (k : ℕ) (t : OTm) (h : t.bvi ≤ k) : (t.clamp k).erase = t
  := by induction t generalizing k with
  | bv =>
    simp only [bvi] at h
    simp only [clamp]
    split
    · rfl
    · omega
  | _ =>
    simp [bvi] at h
    simp [clamp, Tm.erase, *]

@[simp]
def OTm.open (k : ℕ) (x : String) : OTm → OTm
  | .fv x => .fv x
  | .bv i => if i < k then .bv i else if i = k then .fv x else .bv (i - 1)
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.open k x) (b.open k x)
  | .pi A B => .pi (A.open k x) (B.open (k + 1) x)
  | .sigma A B => .sigma (A.open k x) (B.open (k + 1) x)
  | .abs A b => .abs (A.open k x) (b.open (k + 1) x)
  | .app f a => .app (f.open k x) (a.open k x)
  | .pair a b => .pair (a.open k x) (b.open k x)
  | .fst p => .fst (p.open k x)
  | .snd p => .snd (p.open k x)
  | .dite φ l r => .dite (φ.open k x) (l.open (k + 1) x) (r.open (k + 1) x)
  | .trunc A => .trunc (A.open k x)
  | .choose A φ => .choose (A.open k x) (φ.open (k + 1) x)
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.open k x)
  | .natrec C s z n => .natrec (C.open (k + 1) x) (s.open (k + 1) x) (z.open k x) (n.open k x)
  | .has_ty A a => .has_ty (A.open k x) (a.open k x)
  | .invalid => .invalid

theorem Tm.erase_open {k : ℕ} (t : Tm (k + 1)) (x : String) : (t.open x).erase = t.erase.open k x
  := by induction t using Tm.succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp [OTm.open, erase, Tm.open]
  | _ => simp [OTm.open, erase, *]

theorem Tm.clamp_top {k : ℕ} (t : Tm (k + 1)) : t.erase.clamp k = t.lst .invalid
  := by induction t using Tm.succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp [OTm.clamp, Tm.erase, Tm.castLE, Tm.lst]
  | _ => simp [OTm.clamp, Tm.erase, *]

theorem OTm.clamp_succ_lst_invalid {k : ℕ} (t : OTm)
  : (t.clamp (k + 1)).lst .invalid = t.clamp k
  := by induction t generalizing k with
  | bv i =>
    simp only [clamp]
    split
    case isTrue h =>
      generalize hj : Fin.mk i h = j
      have hi : i = j := by cases hj; rfl
      rw [hi]
      cases j using Fin.lastCases <;> simp [Tm.lst, Tm.castLE]
    · simp only [Tm.lst]
      rw [dite_cond_eq_false]
      simp only [eq_iff_iff, iff_false, not_lt]
      omega
  | _ => simp [clamp, *]

theorem OTm.clamp_one (t : OTm)
  : (t.clamp 1).lst .invalid = t.clamp 0
  := t.clamp_succ_lst_invalid

theorem OTm.clamp_succ_open {k : ℕ} (t : OTm) (x : String)
  : (t.clamp (k + 1)).open x = (t.open k x).clamp k
  := by induction t generalizing k with
  | bv i =>
    simp only [clamp]
    split
    case isTrue h =>
      generalize hj : Fin.mk i h = j
      have hi : i = j := by cases hj; rfl
      rw [hi]
      cases j using Fin.lastCases <;> simp [Tm.open, OTm.clamp, OTm.open]
    · simp only [Tm.open_invalid, «open»]
      rw [ite_cond_eq_false]
      · split
        · omega
        · simp [clamp]
          omega
      simp only [eq_iff_iff, iff_false, not_lt]
      omega
  | _ => simp [OTm.open, clamp, *]

@[simp]
def OTm.lst (t : OTm) (k : ℕ) (v : OTm) : OTm := match t with
  | .fv x => .fv x
  | .bv i => if i < k then .bv i else if i = k then v else .bv (i - 1)
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.lst k v) (b.lst k v)
  | .pi A B => .pi (A.lst k v) (B.lst (k + 1) v)
  | .sigma A B => .sigma (A.lst k v) (B.lst (k + 1) v)
  | .abs A b => .abs (A.lst k v) (b.lst (k + 1) v)
  | .app f a => .app (f.lst k v) (a.lst k v)
  | .pair a b => .pair (a.lst k v) (b.lst k v)
  | .fst p => .fst (p.lst k v)
  | .snd p => .snd (p.lst k v)
  | .dite φ l r => .dite (φ.lst k v) (l.lst (k + 1) v) (r.lst (k + 1) v)
  | .trunc A => .trunc (A.lst k v)
  | .choose A φ => .choose (A.lst k v) (φ.lst (k + 1) v)
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.lst k v)
  | .natrec C s z n => .natrec (C.lst (k + 1) v) (s.lst (k + 1) v) (z.lst k v) (n.lst k v)
  | .has_ty A a => .has_ty (A.lst k v) (a.lst k v)
  | .invalid => .invalid

theorem Tm.erase_lst {k : ℕ} (t : Tm (k + 1)) (v : Tm 0) : (t.lst v).erase = t.erase.lst k v.erase
  := by induction t using succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp [Tm.erase, Tm.lst]
  | _ => simp [Tm.erase, *]

theorem OTm.lst_bvi (t : OTm) (k : ℕ) (v : OTm) (h : t.bvi ≤ k) : t.lst k v = t := by
  induction t generalizing k with
  | bv i =>
    simp [bvi] at h
    simp
    intro h; split <;> omega
  | _ =>
    simp [bvi] at h
    simp [*]

theorem OTm.open_bvi (t : OTm) (k : ℕ) (x : String) (h : t.bvi ≤ k) : t.open k x = t := by
  induction t generalizing k with
  | bv i =>
    simp [bvi] at h
    simp [«open»]
    intro h; split <;> omega
  | _ =>
    simp [bvi] at h
    simp [*]

theorem OTm.clamp_lst (k : ℕ) (t : OTm) (v : OTm) (h : v.bvi = 0)
  : (t.lst k v).clamp k = (t.clamp (k + 1)).lst (v.clamp 0) := by induction t generalizing k with
  | bv i =>
    simp only [lst, clamp]
    split
    · simp [clamp, *]
      rw [dite_cond_eq_true]
      case isTrue h =>
        simp [Tm.lst]
        generalize hj : (Fin.mk i (Nat.lt_succ_of_lt h) : Fin (k + 1)) = j
        cases j using Fin.lastCases
        · cases hj; omega
        · cases hj; simp
      simp; omega
    · split
      case isTrue h =>
        cases h
        simp [Tm.lst]
        generalize hj : (Fin.mk i _) = j
        cases j using Fin.lastCases with
        | last =>
          simp
          apply Tm.erase_injective
          simp
          rw [OTm.erase_clamp_bvi_le, OTm.erase_clamp_bvi_le] <;> omega
        | cast j => cases j; simp at hj; omega
      · rw [dite_cond_eq_false]
        · simp [clamp]; omega
        simp; omega
  | _ => simp [clamp, *]

@[simp]
def OTm.wkn (k : ℕ) : OTm → OTm
  | .fv x => .fv x
  | .bv i => if i < k then .bv i else .bv (i + 1)
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.wkn k) (b.wkn k)
  | .pi A B => .pi (A.wkn k) (B.wkn (k + 1))
  | .sigma A B => .sigma (A.wkn k) (B.wkn (k + 1))
  | .abs A b => .abs (A.wkn k) (b.wkn (k + 1))
  | .app f a => .app (f.wkn k) (a.wkn k)
  | .pair a b => .pair (a.wkn k) (b.wkn k)
  | .fst p => .fst (p.wkn k)
  | .snd p => .snd (p.wkn k)
  | .dite φ l r => .dite (φ.wkn k) (l.wkn (k + 1)) (r.wkn (k + 1))
  | .trunc A => .trunc (A.wkn k)
  | .choose A φ => .choose (A.wkn k) (φ.wkn (k + 1))
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.wkn k)
  | .natrec C s z n => .natrec (C.wkn (k + 1)) (s.wkn (k + 1)) (z.wkn k) (n.wkn k)
  | .has_ty A a => .has_ty (A.wkn k) (a.wkn k)
  | .invalid => .invalid

def OTm.Subst : Type := ℕ → OTm

def OTm.Subst.mk (f : ℕ → OTm) : Subst := f

def OTm.Subst.get (σ : Subst) (i : ℕ) : OTm := σ i

@[simp] theorem OTm.Subst.get_mk {f i} : (mk f).get i = f i := rfl

@[ext] theorem OTm.Subst.ext (f g : Subst) (h : ∀ i, f.get i = g.get i) : f = g := funext h

def OTm.Subst.lift (σ : Subst) : Subst := mk (fun | 0 => .bv 0 | i + 1 => (σ.get i).wkn 0)

@[simp] theorem OTm.Subst.lift_get_zero {σ : Subst}
  : σ.lift.get 0 = .bv 0 := rfl

@[simp] theorem OTm.Subst.lift_get_succ {σ : Subst} {i}
  : σ.lift.get (i + 1) = (σ.get i).wkn 0 := rfl

@[simp]
def OTm.subst (σ : Subst) : OTm → OTm
  | .fv x => .fv x
  | .bv i => σ.get i
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.subst σ) (b.subst σ)
  | .pi A B => .pi (A.subst σ) (B.subst σ.lift)
  | .sigma A B => .sigma (A.subst σ) (B.subst σ.lift)
  | .abs A b => .abs (A.subst σ) (b.subst σ.lift)
  | .app f a => .app (f.subst σ) (a.subst σ)
  | .pair a b => .pair (a.subst σ) (b.subst σ)
  | .fst p => .fst (p.subst σ)
  | .snd p => .snd (p.subst σ)
  | .dite φ l r => .dite (φ.subst σ) (l.subst σ.lift) (r.subst σ.lift)
  | .trunc A => .trunc (A.subst σ)
  | .choose A φ => .choose (A.subst σ) (φ.subst σ.lift)
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.subst σ)
  | .natrec C s z n => .natrec (C.subst σ.lift) (s.subst σ.lift) (z.subst σ) (n.subst σ)
  | .has_ty A a => .has_ty (A.subst σ) (a.subst σ)
  | .invalid => .invalid
