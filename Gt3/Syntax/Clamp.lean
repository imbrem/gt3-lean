import Gt3.Syntax.Erase

namespace Gt3

def Tm.clamp {m} (k : ℕ) : Tm m → Tm k
  | .fv x => .fv x
  | .bv i => if h : i < k then .bv (i.castLT h) else .invalid
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
theorem Tm.clamp_refl {k} (t : Tm k) : t.clamp k = t
  := by induction t <;> simp [clamp, Fin.castLT, *]

theorem Tm.erase_clamp {m k : ℕ} (t : Tm m) : (t.erase).clamp k = t.clamp k := by
  induction t generalizing k with
  | bv => rfl
  | _ => simp only [erase, clamp, OTm.clamp, *]

theorem OTm.clamp_clamp {k k' : ℕ} (t : OTm)
  : (t.clamp k).clamp k' = (t.clamp (k ⊓ k')).castLE inf_le_right
  := by induction t generalizing k k' with
  | bv =>
    simp [clamp]; split <;> simp [Tm.clamp, Tm.castLE, *]; split <;> simp [Tm.castLE]
  | _ => simp only [Tm.castLE, Tm.clamp, clamp, *] <;> congr <;> simp

@[simp]
theorem Tm.clamp_clamp {m k k' : ℕ} (t : Tm m)
  : (t.clamp k).clamp k' = (t.clamp (k ⊓ k')).castLE inf_le_right
  := by induction t generalizing k k' with
  | bv => simp [clamp]; split <;> simp [clamp, castLE, *]; split <;> simp [castLE, Fin.castLT]
  | _ => simp only [castLE, clamp, *] <;> congr <;> simp

theorem Tm.clamp_clamp_zero {m k : ℕ} (t : Tm m) : (t.clamp k).clamp 0 = t.clamp 0 := by
  rw [Tm.clamp_clamp, <-(t.clamp 0).castLE_refl]
  congr <;> simp

@[simp]
theorem Tm.clamp_castLE {lo hi k : ℕ} (h : lo ≤ hi) (t : Tm lo)
  : (t.castLE h).clamp k = t.clamp k
  := by induction t generalizing hi k with
  | bv => rfl
  | _ => simp [clamp, castLE, *]

@[simp]
theorem OTm.clamp_clamp_zero {k : ℕ} (t : OTm) : (t.clamp k).clamp 0 = t.clamp 0 := by
  rw [OTm.clamp_clamp, <-(t.clamp 0).castLE_refl]
  congr <;> simp

end Gt3
