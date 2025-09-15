import Gt3.Syntax.Basic

def Tm.wkn {k} (j : ℕ) : Tm k → Tm (k + 1)
  | .fv x => .fv x
  | .bv i => if i < j then .bv i.castSucc else .bv i.succ
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.wkn j) (b.wkn j)
  | .pi A B => .pi (A.wkn j) (B.wkn (j + 1))
  | .sigma A B => .sigma (A.wkn j) (B.wkn (j + 1))
  | .abs A b => .abs (A.wkn j) (b.wkn (j + 1))
  | .app f a => .app (f.wkn j) (a.wkn j)
  | .pair a b => .pair (a.wkn j) (b.wkn j)
  | .fst p => .fst (p.wkn j)
  | .snd p => .snd (p.wkn j)
  | .dite φ l r => .dite (φ.wkn j) (l.wkn (j + 1)) (r.wkn (j + 1))
  | .trunc A => .trunc (A.wkn j)
  | .choose A φ => .choose (A.wkn j) (φ.wkn (j + 1))
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.wkn j)
  | .natrec C s z n => .natrec (C.wkn (j + 1)) (s.wkn (j + 1)) (z.wkn j) (n.wkn j)
  | .has_ty A a => .has_ty (A.wkn j) (a.wkn j)
  | .invalid => .invalid

def Tm.wk0 {k} (t : Tm k) : Tm (k + 1) := t.wkn 0

prefix:1000 "↑₀" => Tm.wk0

theorem Tm.wkn_le {lo hi} (t : Tm lo) (h : lo ≤ hi) : t.wkn hi = ↑₊ t
  := by
  rw [castSucc, castAdd]
  induction t generalizing hi with
  | bv i => simp [wkn, lt_of_lt_of_le i.prop h]; rfl
  | _ => simp [wkn, castLE, *]

theorem Tm.wkn_castLE {lo hi} (h : lo ≤ hi) (t : Tm lo) (j : ℕ)
  : (t.castLE h).wkn j = (t.wkn j).castLE (Nat.succ_le_succ h)
  := by induction t generalizing hi j with
  | bv i => simp [wkn, castLE]; split <;> rfl
  | _ => simp [wkn, castLE, *]

theorem Tm.wkn_lst_le {k j} (t : Tm (k + 1)) (v : Tm 0) (hj : j ≤ k)
  : (t.lst v).wkn j = (t.wkn j).lst v
  := by induction t using succIndOn generalizing j with
  | bv i =>
    cases i using Fin.lastCases with
    | last =>
      simp [wkn, lst_bv, Nat.not_lt_of_le hj]
      rw [Tm.wkn_castLE, Tm.wkn_le _ (Nat.zero_le _), Tm.castSucc, Tm.castAdd, Tm.castLE_castLE]
    | cast i =>
      simp [wkn, lst_bv]
      split <;> simp [lst_bv, <-Fin.castSucc_succ]
  | _ => simp [wkn, *]

theorem Tm.wk0_lst {k} (t : Tm (k + 1)) (v : Tm 0) : ↑₀ (t.lst v) = (↑₀ t).lst v
  := t.wkn_lst_le v (Nat.zero_le _)

@[simp]
theorem Tm.lst_wk0 {k} (t : Tm (k + 1)) (v : Tm 0) : (↑₀ t).lst v = ↑₀ (t.lst v)
  := (t.wk0_lst v).symm

theorem Tm.wkn_open_le {k j} (t : Tm (k + 1)) (x : String) (hj : j ≤ k)
  : (t.open x).wkn j = (t.wkn j).open x
  := by rw [<-Tm.lst_fv, Tm.wkn_lst_le _ _ hj, Tm.lst_fv]

theorem Tm.wk0_open {k} (t : Tm (k + 1)) (x : String) : ↑₀ (t.open x) = (↑₀ t).open x
  := t.wkn_open_le x (Nat.zero_le _)

@[simp]
theorem Tm.open_wk0 {k} (t : Tm (k + 1)) (x : String) : (↑₀ t).open x = ↑₀ (t.open x)
  := (t.wk0_open x).symm

def Tm.arr {k} (A B : Tm k) : Tm k := .pi A (↑₀B)

@[simp]
theorem Tm.lst_arr {k} (A B : Tm (k + 1)) (v : Tm 0)
   : (Tm.arr A B).lst v = .arr (A.lst v) (B.lst v) := by simp [arr]

@[simp]
theorem Tm.open_arr {k} (A B : Tm (k + 1)) (x : String)
  : (Tm.arr A B).open x = .arr (A.open x) (B.open x) := by simp [arr]

def Tm.prod {k} (A B : Tm k) : Tm k := .sigma A (↑₀ B)

@[simp]
theorem Tm.lst_prod {k} (A B : Tm (k + 1)) (v : Tm 0)
   : (Tm.prod A B).lst v = .prod (A.lst v) (B.lst v) := by simp [prod]

@[simp]
theorem Tm.open_prod {k} (A B : Tm (k + 1)) (x : String)
  : (Tm.prod A B).open x = .prod (A.open x) (B.open x) := by simp [prod]
