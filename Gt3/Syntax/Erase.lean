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
  | abs (A B : OTm) (b : OTm) : OTm
  | app (f a : OTm) : OTm
  | pair (a b : OTm) : OTm
  | fst (p : OTm) : OTm
  | snd (p : OTm) : OTm
  | dite (A φ l r : OTm) : OTm
  | trunc (A : OTm) : OTm
  | choose (A φ : OTm) : OTm
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
  | .abs A B b => .abs A.erase B.erase b.erase
  | .app f a => .app f.erase a.erase
  | .pair a b => .pair a.erase b.erase
  | .fst p => .fst p.erase
  | .snd p => .snd p.erase
  | .dite A φ l r => .dite A.erase φ.erase l.erase r.erase
  | .trunc A => .trunc A.erase
  | .choose A φ => .choose A.erase φ.erase
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
  | .abs A B b => .abs (A.clamp k) (B.clamp (k + 1)) (b.clamp (k + 1))
  | .app f a => .app (f.clamp k) (a.clamp k)
  | .pair a b => .pair (a.clamp k) (b.clamp k)
  | .fst p => .fst (p.clamp k)
  | .snd p => .snd (p.clamp k)
  | .dite A φ l r => .dite (A.clamp k) (φ.clamp k) (l.clamp (k + 1)) (r.clamp (k + 1))
  | .trunc A => .trunc (A.clamp k)
  | .choose A φ => .choose (A.clamp k) (φ.clamp (k + 1))
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
  | .abs A B b => A.fvs ∪ B.fvs ∪ b.fvs
  | .app f a => f.fvs ∪ a.fvs
  | .pair a b => a.fvs ∪ b.fvs
  | .fst p => p.fvs
  | .snd p => p.fvs
  | .dite A φ l r => A.fvs ∪ φ.fvs ∪ l.fvs ∪ r.fvs
  | .trunc A => A.fvs
  | .choose A φ => A.fvs ∪ φ.fvs
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
  | .abs A B b => A.bvi ⊔ (B.bvi - 1) ⊔  (b.bvi - 1)
  | .app f a => f.bvi ⊔ a.bvi
  | .pair a b => a.bvi ⊔ b.bvi
  | .fst p => p.bvi
  | .snd p => p.bvi
  | .dite A φ l r => A.bvi ⊔ φ.bvi ⊔ (l.bvi - 1) ⊔ (r.bvi - 1)
  | .trunc A => A.bvi
  | .choose A φ => A.bvi ⊔ (φ.bvi - 1)
  | .has_ty A a => A.bvi ⊔ a.bvi
  | _ => 0

def OTm.bvi : OTm → ℕ
  | .bv i => i + 1
  | .eqn a b => a.bvi ⊔ b.bvi
  | .pi A B => A.bvi ⊔ (B.bvi - 1)
  | .sigma A B => A.bvi ⊔ (B.bvi - 1)
  | .abs A B b => A.bvi ⊔ (B.bvi - 1) ⊔ (b.bvi - 1)
  | .app f a => f.bvi ⊔ a.bvi
  | .pair a b => a.bvi ⊔ b.bvi
  | .fst p => p.bvi
  | .snd p => p.bvi
  | .dite A φ l r => A.bvi ⊔ φ.bvi ⊔ (l.bvi - 1) ⊔ (r.bvi - 1)
  | .trunc A => A.bvi
  | .choose A φ => A.bvi ⊔ (φ.bvi - 1)
  | .has_ty A a => A.bvi ⊔ a.bvi
  | _ => 0

theorem Tm.bvi_le {k : ℕ} (t : Tm k) : t.bvi ≤ k
  := by induction t <;> simp only [bvi, sup_le_iff] <;> omega

theorem Tm.bvi_erase {k : ℕ} (t : Tm k) : t.erase.bvi = t.bvi
  := by induction t <;> simp [bvi, erase, OTm.bvi, *]

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
