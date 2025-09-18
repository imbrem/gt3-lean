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
  := by rw [<-Tm.lst_of_fv, Tm.wkn_lst_le _ _ hj, Tm.lst_of_fv]

theorem Tm.wk0_open {k} (t : Tm (k + 1)) (x : String) : ↑₀ (t.open x) = (↑₀ t).open x
  := t.wkn_open_le x (Nat.zero_le _)

@[simp]
theorem Tm.open_wk0_succ {k} (t : Tm (k + 1)) (x : String) : (↑₀ t).open x = ↑₀ (t.open x)
  := (t.wk0_open x).symm

theorem Tm.wkn_castLE_le {lo hi} (h : lo ≤ hi) (t : Tm lo) (j : ℕ) (hj : lo ≤ j)
  : (t.castLE h).wkn j = t.castLE (by omega)
  := by induction t generalizing hi j <;> simp [wkn, castLE, *]; intro; omega

@[simp]
theorem Tm.wkn_castLE_eq {lo hi} (h : lo ≤ hi) (t : Tm lo)
  : (t.castLE h).wkn lo = t.castLE (by omega)
  := t.wkn_castLE_le h lo (le_refl lo)

@[simp]
theorem Tm.wkn_castLE_zero {k} (t : Tm 0) (j : ℕ)
  : (t.castLE (Nat.zero_le k)).wkn j = t.castLE (Nat.zero_le _)
  := t.wkn_castLE_le (Nat.zero_le _) _ (Nat.zero_le _)

@[simp]
theorem Tm.wk0_cast_zero {k} (t : Tm 0)
  : (t.castLE (Nat.zero_le k)).wk0 = t.castLE (Nat.zero_le _)
  := t.wkn_castLE_eq (Nat.zero_le _)

@[simp]
theorem Tm.wk0_tm_zero (t : Tm 0) : t.wk0 = t.castLE (Nat.zero_le 1)
  := by convert t.wk0_cast_zero; simp

theorem Tm.open_wk0 (t : Tm 0) (x : String) : (↑₀ t).open x = t
  := by simp

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

def Tm.ite {k} (φ l r : Tm k) : Tm k := .dite φ (↑₀ l) (↑₀ r)

@[simp]
theorem Tm.lst_ite {k} (φ l r : Tm (k + 1)) (v : Tm 0)
   : (Tm.ite φ l r).lst v = .ite (φ.lst v) (l.lst v) (r.lst v) := by simp [ite]

@[simp]
theorem Tm.open_ite {k} (φ l r : Tm (k + 1)) (x : String)
  : (Tm.ite φ l r).open x = .ite (φ.open x) (l.open x) (r.open x) := by simp [ite]

@[simp]
def Tm.st {k : ℕ} (t : Tm (k + 1)) (v : Tm k) : Tm k := match t with
  | .fv y => .fv y
  | .bv i => i.lastCases v .bv
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.st v) (b.st v)
  | .pi A B => .pi (A.st v) (B.st (↑₀ v))
  | .sigma A B => .sigma (A.st v) (B.st (↑₀ v))
  | .abs A b => .abs (A.st v) (b.st (↑₀ v))
  | .app f a => .app (f.st v) (a.st v)
  | .pair a b => .pair (a.st v) (b.st v)
  | .fst p => .fst (p.st v)
  | .snd p => .snd (p.st v)
  | .dite φ l r => .dite (φ.st v) (l.st (↑₀ v)) (r.st (↑₀ v))
  | .trunc A => .trunc (A.st v)
  | .choose A φ => .choose (A.st v) (φ.st (↑₀ v))
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.st v)
  | .natrec C s z n => .natrec (C.st (↑₀ v)) (s.st (↑₀ v)) (z.st v) (n.st v)
  | .has_ty A a => .has_ty (A.st v) (a.st v)
  | .invalid => .invalid

theorem Tm.st_cast_zero {k} (t : Tm (k + 1)) (v : Tm 0)
  : t.st (v.castLE (Nat.zero_le _)) = t.lst v := by
  induction t using succIndOn <;> simp [lst, *]

theorem Tm.cast_le_st {lo hi} (h : lo < hi + 1) (t : Tm lo) (v : Tm hi)
  : (t.castLE (le_of_lt h)).st v = t.castLE (Nat.le_of_succ_le_succ h)
  := by induction t generalizing hi v with
  | bv i =>
    simp [castLE]
    cases i
    generalize hw : Fin.castLE _ _ = w
    cases w using Fin.lastCases with
    | last => simp [Fin.last] at hw; omega
    | cast i => cases hw; simp
  | _ => simp [castLE, *]

@[simp]
theorem Tm.cast_zero_st {k} (t : Tm 0) (v : Tm k)
  : (t.castLE (Nat.zero_le (k + 1))).st v = t.castLE (Nat.zero_le k)
  := t.cast_le_st (Nat.zero_lt_succ k) v

def Tm.sth {k} (t : Tm (k + 1)) (v : Tm (k + 1)) : Tm (k + 1) := (t.wkn k).st v

theorem Tm.lst_sth {k} (t : Tm (k + 1)) (h : Tm (k + 1)) (v : Tm 0)
  : (t.sth h).lst v = t.st (h.lst v)
  := by
  simp only [sth]
  induction t using succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp [wkn, lst]
  | _ => simp [wkn, *]

theorem Tm.open_sth {k} (t : Tm (k + 1)) (h : Tm (k + 1)) (x : String)
  : (t.sth h).open x = t.st (h.open x)
  := by rw [<-Tm.lst_of_fv, Tm.lst_sth, Tm.lst_of_fv]

def Tm.succIn {k} (t : Tm (k + 1)) : Tm (k + 1) := t.sth (.succ (.bv (Fin.last k)))

theorem Tm.lst_succIn {k} (t : Tm (k + 1)) (v : Tm 0)
  : (t.succIn).lst v = t.lst (.succ v)
  := by simp [succIn, lst, lst_sth]; rw [<-st_cast_zero]; rfl

theorem Tm.open_succIn {k} (t : Tm (k + 1)) (x : String)
  : (t.succIn).open x = t.lst (.succ (.fv x))
  := by rw [<-lst_of_fv, lst_succIn]

@[simp]
theorem Tm.wkn_get {k} (σ : VSubst) (x : String) (j : ℕ)
  : (σ.get (k := k) x).wkn j = σ.get x
  := by simp [VSubst.get]

@[simp]
theorem Tm.st_get {k} (σ : VSubst) (x : String) (v : Tm k)
  : (σ.get x).st v = σ.get x
  := by simp [VSubst.get]

theorem Tm.smul_wkn {k} (σ : VSubst) (j : ℕ) (t : Tm k)
  : σ • (t.wkn j) = (σ • t).wkn j
  := by induction t generalizing j <;> simp [wkn, *]

@[simp]
theorem Tm.smul_wk0 (σ : VSubst) {k} (t : Tm k)
  : σ • (↑₀ t) = ↑₀ (σ • t)
  := t.smul_wkn σ 0

@[simp]
theorem Tm.smul_arr (σ : VSubst) {k} (A B : Tm k)
  : σ • (Tm.arr A B) = Tm.arr (σ • A) (σ • B)
  := by simp [arr]

@[simp]
theorem Tm.smul_prod (σ : VSubst) {k} (A B : Tm k)
  : σ • (Tm.prod A B) = Tm.prod (σ • A) (σ • B)
  := by simp [prod]

theorem Tm.smul_st (σ : VSubst) {k} (t : Tm (k + 1)) (v : Tm k)
  : σ • (t.st v) = (σ • t).st (σ • v)
  := by induction t using succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp
  | _ => simp [st, *]

theorem Tm.smul_succIn (σ : VSubst) {k} (t : Tm (k + 1))
  : σ • t.succIn = (σ • t).succIn
  := by rw [succIn, sth, smul_st, smul_wkn]; rfl

def Tm.succArrow {k} (C : Tm (k + 1)) : Tm (k + 1) := .arr C C.succIn

theorem Tm.lst_succArrow {k} (C : Tm (k + 1)) (v : Tm 0)
  : (Tm.succArrow C).lst v = .arr (C.lst v) (C.lst (.succ v))
  := by simp [succArrow, lst_succIn]

theorem Tm.open_succArrow {k} (C : Tm (k + 1)) (x : String)
  : (Tm.succArrow C).open x = .arr (C.open x) (C.lst (.succ (.fv x)))
  := by simp [succArrow, open_succIn]

theorem Tm.smul_succArrow (σ : VSubst) {k} (C : Tm (k + 1))
  : σ • (Tm.succArrow C) = Tm.succArrow (σ • C)
  := by simp [succArrow, smul_succIn, smul_arr]

theorem Tm.smul_succArrow_open (σ : VSubst) {k} (C : Tm (k + 1)) (x : String) (hx : σ.IdAt x)
  : σ • ((Tm.succArrow C).open x) = (Tm.succArrow (σ • C)).open x
  := by rw [ls_open, smul_succArrow, lst_succArrow, hx, open_succArrow, lst_of_fv]
