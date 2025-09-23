import Gt3.Syntax.Subst

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

theorem OTm.bvi_open_le
  (k : ℕ) (t : OTm) (x : String) (h : t.bvi ≤ k) : (t.open k x).bvi ≤ k := by
  induction t generalizing k with
  | bv i => simp; split_ifs <;> simp [bvi] at * <;> omega
  | _ => simp [bvi] at * <;> grind

theorem OTm.bvi_of_open_le
  (k : ℕ) (t : OTm) (x : String) (h : (t.open k x).bvi ≤ k) : t.bvi ≤ k + 1 := by
  induction t generalizing k with
  | bv i => simp [bvi] at *; split_ifs at h <;> simp [bvi] at * <;> omega
  | _ => simp [bvi] at * <;> grind

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

theorem OTm.lst_of_fv (k : ℕ) (x : String) (t : OTm)
  : t.lst k (.fv x) = t.open k x := by induction t generalizing k <;> simp [*]

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

theorem OTm.wkn_of_bvi_le (k : ℕ) (t : OTm) (h : t.bvi ≤ k) : t.wkn k = t := by
  induction t generalizing k <;> grind [wkn, bvi]

theorem OTm.clamp_wkn_succ_le (lo hi : ℕ) (t : OTm) (h : lo ≤ hi)
  : (t.wkn lo).clamp (hi + 1) = (t.clamp hi).wkn lo := by
  induction t generalizing lo hi with
  | bv i =>
    simp only [wkn, clamp]
    split_ifs
    · simp [Tm.wkn, clamp, *]
      split
      · simp
      · omega
    · simp [Tm.wkn, clamp]; omega
    · simp [Tm.wkn, clamp, *]
    · simp [Tm.wkn, clamp]; omega
  | _ => simp [wkn, clamp, Tm.wkn, *]

@[simp]
def OTm.close (k : ℕ) (x : String) : OTm → OTm
  | .fv y => if x = y then .bv k else .fv y
  | .bv i => if i < k then .bv i else .bv (i + 1)
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.close k x) (b.close k x)
  | .pi A B => .pi (A.close k x) (B.close (k + 1) x)
  | .sigma A B => .sigma (A.close k x) (B.close (k + 1) x)
  | .abs A b => .abs (A.close k x) (b.close (k + 1) x)
  | .app f a => .app (f.close k x) (a.close k x)
  | .pair a b => .pair (a.close k x) (b.close k x)
  | .fst p => .fst (p.close k x)
  | .snd p => .snd (p.close k x)
  | .dite φ l r => .dite (φ.close k x) (l.close (k + 1) x) (r.close (k + 1) x)
  | .trunc A => .trunc (A.close k x)
  | .choose A φ => .choose (A.close k x) (φ.close (k + 1) x)
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.close k x)
  | .natrec C s z n
    => .natrec (C.close (k + 1) x) (s.close (k + 1) x)
               (z.close k x) (n.close k x)
  | .has_ty A a => .has_ty (A.close k x) (a.close k x)
  | .invalid => .invalid

@[simp]
def OTm.lsv (t : OTm) (x : String) (v : OTm) : OTm := match t with
  | .fv y => if x = y then v else .fv y
  | .bv i => .bv i
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.lsv x v) (b.lsv x v)
  | .pi A B => .pi (A.lsv x v) (B.lsv x v)
  | .sigma A B => .sigma (A.lsv x v) (B.lsv x v)
  | .abs A b => .abs (A.lsv x v) (b.lsv x v)
  | .app f a => .app (f.lsv x v) (a.lsv x v)
  | .pair a b => .pair (a.lsv x v) (b.lsv x v)
  | .fst p => .fst (p.lsv x v)
  | .snd p => .snd (p.lsv x v)
  | .dite φ l r => .dite (φ.lsv x v) (l.lsv x v) (r.lsv x v)
  | .trunc A => .trunc (A.lsv x v)
  | .choose A φ => .choose (A.lsv x v) (φ.lsv x v)
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.lsv x v)
  | .natrec C s z n => .natrec (C.lsv x v) (s.lsv x v) (z.lsv x v) (n.lsv x v)
  | .has_ty A a => .has_ty (A.lsv x v) (a.lsv x v)
  | .invalid => .invalid

theorem OTm.clamp_lsv (t : OTm) (x : String) (v : OTm) (k) (hv : v.bvi = 0)
  : (t.lsv x v).clamp k = (t.clamp k).lsv x (v.clamp 0) := by
  induction t generalizing k with
  | fv y => simp [lsv, clamp]; split <;> simp [Tm.lsv, clamp, *]
            ; apply Tm.erase_injective ; simp
            ; rw [OTm.erase_clamp_bvi_le, OTm.erase_clamp_bvi_le] <;> omega
  | bv i => simp [lsv, clamp]; split <;> simp [Tm.lsv, *]
  | _ => simp [lsv, clamp, Tm.lsv, *]

theorem Tm.erase_lsv {k : ℕ} (t : Tm k) (x : String) (v : Tm 0)
  : (t.lsv x v).erase = t.erase.lsv x v.erase
  := by induction t with
  | fv y => simp [Tm.lsv, Tm.erase]; split <;> simp [Tm.erase]
  | _ => simp [erase, Tm.lsv, OTm.lsv, *]

@[simp]
theorem OTm.close_open (k : ℕ) (t : OTm) (x y : String)
  : (t.close k x).open k y = t.lsv x (.fv y) := by
  induction t generalizing k with
  | fv => simp; split <;> simp [*]
  | bv i => simp; split <;> simp [*]; rw [ite_cond_eq_false, ite_cond_eq_false] <;> simp <;> omega
  | _ => simp [close, «open», *]

@[simp]
theorem OTm.open_close (k : ℕ) (t : OTm) (x : String) (hx : x ∉ t.fvs)
  : (t.open k x).close k x = t := by
  induction t generalizing k with
  | fv y => convert hx; simp [fvs]
  | bv i =>
    simp [«open»]; split
    · simp [*]
    · split <;> simp [*]; rw [ite_cond_eq_false] <;> simp <;> omega
  | _ =>
    simp [close, «open», *] <;> (try constructorm* _ ∧ _)
    <;> apply_assumption <;> (try simp [fvs] at hx) <;> simp [*]

@[simp]
theorem OTm.close_close_self (m n : ℕ) (t : OTm) (x : String)
  : (t.close m x).close n x = (t.close m x).wkn n := by
  induction t generalizing m n <;> simp [*] <;> split <;> simp [*]

@[simp]
theorem OTm.open_wkn (k : ℕ) (t : OTm) (x : String)
  : (t.wkn k).open k x = t := by
  induction t generalizing k with
  | bv i => simp; split <;> simp [*]; split <;> simp [*] <;> omega
  | _ => simp [*]

@[simp]
def OTm.st (t : OTm) (k : ℕ) (v : OTm) : OTm := match t with
  | .fv x => .fv x
  | .bv i => if i < k then .bv i else if i = k then v else .bv (i - 1)
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.st k v) (b.st k v)
  | .pi A B => .pi (A.st k v) (B.st (k + 1) (v.wkn 0))
  | .sigma A B => .sigma (A.st k v) (B.st (k + 1) (v.wkn 0))
  | .abs A b => .abs (A.st k v) (b.st (k + 1) (v.wkn 0))
  | .app f a => .app (f.st k v) (a.st k v)
  | .pair a b => .pair (a.st k v) (b.st k v)
  | .fst p => .fst (p.st k v)
  | .snd p => .snd (p.st k v)
  | .dite φ l r => .dite (φ.st k v) (l.st (k + 1) (v.wkn 0)) (r.st (k + 1) (v.wkn 0))
  | .trunc A => .trunc (A.st k v)
  | .choose A φ => .choose (A.st k v) (φ.st (k + 1) (v.wkn 0))
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.st k v)
  | .natrec C s z n
    => .natrec (C.st (k + 1) (v.wkn 0)) (s.st (k + 1) (v.wkn 0)) (z.st k v) (n.st k v)
  | .has_ty A a => .has_ty (A.st k v) (a.st k v)
  | .invalid => .invalid

theorem OTm.st_bvi (t : OTm) (k : ℕ) (v : OTm) (h : t.bvi ≤ k) : t.st k v = t := by
  induction t generalizing k v with
  | bv i =>
    simp [bvi] at h
    simp
    intro h; split <;> omega
  | _ =>
    simp [bvi] at h
    simp [*]

theorem OTm.st_eq_lst (t : OTm) (k : ℕ) (v : OTm) (hv : v.bvi = 0)
  : t.st k v = t.lst k v := by
  have hv' := v.wkn_of_bvi_le 0 (by simp [hv])
  induction t generalizing k v <;> simp [*]

theorem Tm.erase_wkn {k : ℕ} (t : Tm k) (n : ℕ)
  : (t.wkn n).erase = t.erase.wkn n
  := by induction t generalizing n with
  | bv i => simp [Tm.erase, OTm.wkn, wkn]; split_ifs <;> rfl
  | _ => simp [Tm.erase, OTm.wkn, wkn, *]

theorem Tm.erase_st {k : ℕ} (t : Tm (k + 1)) (v : Tm k)
  : (t.st v).erase = t.erase.st k v.erase
  := by induction t using Tm.succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp [Tm.erase, Tm.st]
  | _ => simp [Tm.erase, Tm.wk0, Tm.erase_wkn, *]

theorem OTm.st_wkn (t : OTm) (k : ℕ) (v : OTm) (ht : t.bvi ≤ k + 1)
  : (t.wkn k).st (k + 1) v = t.st k v := by
  induction t generalizing k v with
  | bv i =>
    simp [st, wkn]
    split_ifs
    · simp; intro; omega
    · simp [*]
    · simp [bvi] at ht; omega
  | _ =>
    (try simp [bvi] at ht)
    simp [st, wkn] <;> (try constructorm* _ ∧ _) <;> apply_assumption <;> simp [*]

theorem OTm.bvi_wkn (t : OTm) (k : ℕ) (ht : t.bvi ≤ k)
  : (t.wkn k).bvi ≤ k + 1 := by
  induction t generalizing k with
  | bv i => simp; split_ifs <;> simp [bvi] at * <;> omega
  | _ => simp [bvi] at * <;> grind

-- theorem OTm.bvi_st_of_le (t : OTm) (k : ℕ) (v : OTm) (l) (ht : t.bvi ≤ l) (hv : v.bvi ≤ l)
--   : (t.st k v).bvi ≤ l := by
--   --have hv₀ : (v.wkn 0).bvi ≤ l + 1 := sorry
--   induction t generalizing k v l with
--   | bv i => stop simp [st]; split_ifs <;> simp [bvi] at * <;> omega
--   | natrec =>
--     simp [bvi] at ht
--     simp [bvi] <;> (try constructorm* _ ∧ _) <;> apply_assumption <;> simp [*]
--   | _ =>
--     stop
--     simp only [st, bvi, max_le_iff]
--     sorry

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

def OTm.arr (A B : OTm) : OTm := .pi A (B.wkn 0)

def OTm.exists (A φ : OTm) : OTm := .trunc (.sigma A φ)

theorem OTm.open_wkn_succ_le {lo hi} (h : lo ≤ hi) (t : OTm) (x : String)
  : (t.wkn lo).open (hi + 1) x = (t.open hi x).wkn lo
  := by induction t generalizing lo hi with
  | bv i =>
    simp [«open»]
    split_ifs
    · simp only [«open», wkn]; split_ifs <;> first | rfl | omega
    · omega
    · simp only [«open», wkn]; split_ifs <;> first | rfl | omega
    · simp [*]
    · simp [*]
    · simp only [«open», wkn]; split_ifs <;> (try simp) <;> omega
  | _ => simp [*]

theorem OTm.open_arr (A B : OTm) (k : ℕ) (x : String)
  : (A.arr B).open k x = (A.open k x).arr (B.open k x) := by
  simp [arr, «open», OTm.open_wkn_succ_le]

def OTm.not (φ : OTm) : OTm := .eqn φ .empty

theorem OTm.clamp_arr (A B : OTm) (k : ℕ)
  : (A.arr B).clamp k = (A.clamp k).arr (B.clamp k) := by
  simp only [arr, clamp, Nat.zero_le, clamp_wkn_succ_le]; rfl

def OTm.sth (t : OTm) (k : ℕ) (v : OTm) := (t.wkn k).st (k + 1) v

theorem Tm.erase_sth {k : ℕ} (t : Tm (k + 1)) (v : Tm (k + 1))
  : (t.sth v).erase = t.erase.sth k v.erase
  := by simp only [sth, erase_st, erase_wkn, OTm.sth]

def OTm.succIn (t : OTm) (k : ℕ) : OTm := t.sth k (OTm.bv k).succ

theorem Tm.erase_succIn {k : ℕ} (t : Tm (k + 1))
  : (t.succIn).erase = t.erase.succIn k
  := by simp only [succIn, erase_sth, erase, Fin.val_last, OTm.succIn]

def OTm.succArrow (A : OTm) (k : ℕ) : OTm := A.arr (A.succIn k)

theorem OTm.succArrow_zero (A : OTm) (hA : A.bvi ≤ 1)
  : A.succArrow 0 = A.arr (A.st 0 (OTm.bv 0).succ) := by
  simp [succArrow, succIn, sth]
  rw [A.st_wkn]
  exact hA

theorem Tm.erase_arr {k : ℕ} (A B : Tm k)
  : (A.arr B).erase = A.erase.arr B.erase
  := by simp only [arr, wk0, erase, erase_wkn, OTm.arr]

theorem Tm.erase_succArrow {k : ℕ} (A : Tm (k + 1))
  : A.succArrow.erase = A.erase.succArrow k
  := by simp only [succArrow, erase_arr, erase_succIn, OTm.succArrow]

theorem OTm.open_succIn (t : OTm) (k : ℕ) (x : String)
  : (t.succIn k).open k x = (t.lst k (OTm.fv x).succ) := by
  simp only [succIn, sth]
  induction t generalizing k with
  | bv i => repeat first | omega | simp [*] | split_ifs
  | _ => simp [*]

theorem OTm.open_succArrow (A : OTm) (k : ℕ) (x : String)
  : (A.succArrow k).open k x = (A.open k x).arr (A.lst k (OTm.fv x).succ) := by
  simp only [succArrow, open_arr, open_succIn]
