-- To add a new term former; follow the instructions in `TERM_FORMER_CHECKLIST.md`

import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Algebra.Group.Action.Defs

inductive Tm : ℕ → Type
  | fv {k : ℕ} (x : String) : Tm k
  | bv {k : ℕ} (i : Fin k) : Tm k
  | univ {k : ℕ} (ℓ : ℕ) : Tm k
  | empty {k : ℕ} : Tm k
  | unit {k : ℕ} : Tm k
  | null {k : ℕ} : Tm k
  | eqn {k : ℕ} (a b : Tm k) : Tm k
  | pi {k : ℕ} (A : Tm k) (B : Tm (k + 1)) : Tm k
  | sigma {k : ℕ} (A : Tm k) (B : Tm (k + 1)) : Tm k
  | abs {k : ℕ} (A : Tm k) (b : Tm (k + 1)) : Tm k
  | app {k : ℕ} (f a : Tm k) : Tm k
  | pair {k : ℕ} (a : Tm k) (b : Tm k) : Tm k
  | fst {k : ℕ} (p : Tm k) : Tm k
  | snd {k : ℕ} (p : Tm k) : Tm k
  | dite {k : ℕ} (φ : Tm k) (l r : Tm (k + 1)) : Tm k
  | trunc {k : ℕ} (A : Tm k) : Tm k
  | choose {k : ℕ} (A : Tm k) (φ : Tm (k + 1)) : Tm k
  | nats {k : ℕ} : Tm k
  | zero {k : ℕ} : Tm k
  | succ {k : ℕ} (n : Tm k) : Tm k
  | natrec {k : ℕ} (C s : Tm (k + 1)) (z n : Tm k) : Tm k
  | has_ty {k : ℕ} (A a : Tm k) : Tm k
  | invalid {k : ℕ} : Tm k

def Tm.castLE {n m : ℕ} (h : n ≤ m) : Tm n → Tm m
  | .fv x => .fv x
  | .bv i => .bv (i.castLE h)
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.castLE h) (b.castLE h)
  | .pi A B => .pi (A.castLE h) (B.castLE (by omega))
  | .sigma A B => .sigma (A.castLE h) (B.castLE (by omega))
  | .abs A b => .abs (A.castLE h) (b.castLE (by omega))
  | .app f a => .app (f.castLE h) (a.castLE h)
  | .pair a b => .pair (a.castLE h) (b.castLE h)
  | .fst p => .fst (p.castLE h)
  | .snd p => .snd (p.castLE h)
  | .dite φ l r => .dite (φ.castLE h) (l.castLE (by omega)) (r.castLE (by omega))
  | .trunc A => .trunc (A.castLE h)
  | .choose A φ => .choose (A.castLE h) (φ.castLE (by omega))
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.castLE h)
  | .natrec C s z n => .natrec (C.castLE (by omega)) (s.castLE (by omega)) (z.castLE h) (n.castLE h)
  | .has_ty A a => .has_ty (A.castLE h) (a.castLE h)
  | .invalid => .invalid

@[simp]
theorem Tm.castLE_refl {k : ℕ} (t : Tm k) : t.castLE (le_refl k) = t
  := by induction t <;> simp [castLE, *]

@[simp]
theorem Tm.castLE_castLE {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) (t : Tm n)
  : (t.castLE h).castLE h' = t.castLE (h.trans h')
  := by induction t generalizing m k <;> simp [castLE, *]

def Tm.castAdd {k : ℕ} (t : Tm k) (n : ℕ) : Tm (k + n) := t.castLE (by omega)

@[simp]
theorem Tm.castAdd_zero {k : ℕ} (t : Tm k) : t.castAdd 0 = t := t.castLE_refl

def Tm.castSucc {k : ℕ} (t : Tm k) : Tm (k + 1) := t.castAdd 1

prefix:1000 "↑₊" => Tm.castSucc

-- instance Tm.coeSucc {k : ℕ} : Coe (Tm k) (Tm (k + 1)) where
--   coe := castSucc

-- theorem Tm.coe_eqn {k : ℕ} (a b : Tm k) : (Tm.eqn a b : Tm (k + 1)) = .eqn a b
--   := rfl

-- theorem Tm.coe_pi {k : ℕ} (A : Tm k) (B : Tm (k + 1))
--   : (Tm.pi A B : Tm (k + 1)) = .pi A B
--   := rfl

-- theorem Tm.coe_abs {k : ℕ} (A : Tm k) (b : Tm (k + 1))
--   : (Tm.abs A b : Tm (k + 1)) = .abs A b
--   := rfl

-- theorem Tm.coe_app {k : ℕ} (f : Tm k) (a : Tm k)
--   : (Tm.app f a : Tm (k + 1)) = .app f a
--   := rfl

theorem Tm.castAdd_succ {k : ℕ} (t : Tm k) (n : ℕ)
  : t.castAdd (n + 1) = (t.castAdd n).castSucc
  := by simp [castAdd, castSucc]

def Tm.open {k : ℕ} (t : Tm (k + 1)) (x : String) : Tm k := match t with
  | .fv y => .fv y
  | .bv i => i.lastCases (.fv x) .bv
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.open x) (b.open x)
  | .pi A B => .pi (A.open x) (B.open x)
  | .sigma A B => .sigma (A.open x) (B.open x)
  | .abs A b => .abs (A.open x) (b.open x)
  | .app f a => .app (f.open x) (a.open x)
  | .pair a b => .pair (a.open x) (b.open x)
  | .fst p => .fst (p.open x)
  | .snd p => .snd (p.open x)
  | .dite φ l r => .dite (φ.open x) (l.open x) (r.open x)
  | .trunc A => .trunc (A.open x)
  | .choose A φ => .choose (A.open x) (φ.open x)
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.open x)
  | .natrec C z s n => .natrec (C.open x) (z.open x) (s.open x) (n.open x)
  | .has_ty A a => .has_ty (A.open x) (a.open x)
  | .invalid => .invalid

@[simp]
theorem Tm.open_fv {k : ℕ} {y x : String} : (Tm.fv (k := (k + 1)) y).open x = .fv y
  := by simp [«open»]

theorem Tm.open_bv {k : ℕ} (i : Fin (k + 1)) (x : String)
  : (Tm.bv (k := (k + 1)) i).open x = i.lastCases (.fv x) .bv
  := by simp [«open»]

@[simp]
theorem Tm.open_univ {k : ℕ} (ℓ : ℕ) (x : String)
  : (Tm.univ (k := (k + 1)) ℓ).open x = .univ ℓ
  := by simp [«open»]

@[simp]
theorem Tm.open_null {k : ℕ} (x : String) : (Tm.null (k := (k + 1))).open x = .null
  := by simp [«open»]

@[simp]
theorem Tm.open_empty {k : ℕ} (x : String) : (Tm.empty (k := (k + 1))).open x = .empty
  := by simp [«open»]

@[simp]
theorem Tm.open_unit {k : ℕ} (x : String) : (Tm.unit (k := (k + 1))).open x = .unit
  := by simp [«open»]

@[simp]
theorem Tm.open_eqn {k : ℕ} (a b : Tm (k + 1)) (x : String)
  : (Tm.eqn (k := (k + 1)) a b).open x = .eqn (a.open x) (b.open x)
  := by simp [«open»]

@[simp]
theorem Tm.open_pi {k : ℕ} (A : Tm (k + 1)) (B : Tm (k + 2)) (x : String)
  : (Tm.pi (k := (k + 1)) A B).open x = .pi (A.open x) (B.open x)
  := by simp [«open»]

@[simp]
theorem Tm.open_sigma {k : ℕ} (A : Tm (k + 1)) (B : Tm (k + 2)) (x : String)
  : (Tm.sigma (k := (k + 1)) A B).open x = .sigma (A.open x) (B.open x)
  := by simp [«open»]

@[simp]
theorem Tm.open_abs {k : ℕ} (A : Tm (k + 1)) (b : Tm (k + 2)) (x : String)
  : (Tm.abs (k := (k + 1)) A b).open x = .abs (A.open x) (b.open x)
  := by simp [«open»]

@[simp]
theorem Tm.open_app {k : ℕ} (f a : Tm (k + 1)) (x : String)
  : (Tm.app (k := (k + 1)) f a).open x = .app (f.open x) (a.open x)
  := by simp [«open»]

@[simp]
theorem Tm.open_pair {k : ℕ} (a b : Tm (k + 1)) (x : String)
  : (Tm.pair (k := (k + 1)) a b).open x = .pair (a.open x) (b.open x)
  := by simp [«open»]

@[simp]
theorem Tm.open_fst {k : ℕ} (p : Tm (k + 1)) (x : String)
  : (Tm.fst (k := (k + 1)) p).open x = .fst (p.open x)
  := by simp [«open»]

@[simp]
theorem Tm.open_snd {k : ℕ} (p : Tm (k + 1)) (x : String)
  : (Tm.snd (k := (k + 1)) p).open x = .snd (p.open x)
  := by simp [«open»]

@[simp]
theorem Tm.open_dite {k : ℕ} (φ : Tm (k + 1)) (l r : Tm (k + 2)) (x : String)
  : (Tm.dite (k := (k + 1)) φ l r).open x = .dite (φ.open x) (l.open x) (r.open x)
  := by simp [«open»]

@[simp]
theorem Tm.open_trunc {k : ℕ} (A : Tm (k + 1)) (x : String)
  : (Tm.trunc (k := (k + 1)) A).open x = .trunc (A.open x)
  := by simp [«open»]

@[simp]
theorem Tm.open_choose {k : ℕ} (A : Tm (k + 1)) (φ : Tm (k + 2)) (x : String)
  : (Tm.choose (k := (k + 1)) A φ).open x = .choose (A.open x) (φ.open x)
  := by simp [«open»]

@[simp]
theorem Tm.open_nats {k : ℕ} (x : String) : (Tm.nats (k := (k + 1))).open x = .nats
  := by simp [«open»]

@[simp]
theorem Tm.open_zero {k : ℕ} (x : String) : (Tm.zero (k := (k + 1))).open x = .zero
  := by simp [«open»]

@[simp]
theorem Tm.open_succ {k : ℕ} (n : Tm (k + 1)) (x : String)
  : (Tm.succ (k := (k + 1)) n).open x = .succ (n.open x)
  := by simp [«open»]

@[simp]
theorem Tm.open_natrec {k : ℕ} (C : Tm (k + 2)) (s : Tm (k + 2)) (z : Tm (k + 1)) (n : Tm (k + 1))
  (x : String) : (Tm.natrec (k := (k + 1)) C s z n).open x =
  .natrec (C.open x) (s.open x) (z.open x) (n.open x) := by simp [«open»]

@[simp]
theorem Tm.open_has_ty {k : ℕ} (A a : Tm (k + 1)) (x : String)
  : (Tm.has_ty (k := (k + 1)) A a).open x = .has_ty (A.open x) (a.open x)
  := by simp [«open»]

@[simp]
theorem Tm.open_invalid {k : ℕ} (x : String) : (Tm.invalid (k := (k + 1))).open x = .invalid
  := by simp [«open»]

def Tm.lst {k : ℕ} (t : Tm (k + 1)) (v : Tm 0) : Tm k := match t with
  | .fv y => .fv y
  | .bv i => i.lastCases (v.castLE (by omega)) .bv
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.lst v) (b.lst v)
  | .pi A B => .pi (A.lst v) (B.lst v)
  | .sigma A B => .sigma (A.lst v) (B.lst v)
  | .abs A b => .abs (A.lst v) (b.lst v)
  | .app f a => .app (f.lst v) (a.lst v)
  | .pair a b => .pair (a.lst v) (b.lst v)
  | .fst p => .fst (p.lst v)
  | .snd p => .snd (p.lst v)
  | .dite φ l r => .dite (φ.lst v) (l.lst v) (r.lst v)
  | .trunc A => .trunc (A.lst v)
  | .choose A φ => .choose (A.lst v) (φ.lst v)
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.lst v)
  | .natrec C s z n => .natrec (C.lst v) (s.lst v) (z.lst v) (n.lst v)
  | .has_ty A a => .has_ty (A.lst v) (a.lst v)
  | .invalid => .invalid

@[simp]
theorem Tm.lst_fv {k : ℕ} (x : String) (v : Tm 0)
  : (Tm.fv (k := (k + 1)) x).lst v = .fv x
  := by simp [lst]

theorem Tm.lst_bv {k : ℕ} (i : Fin (k + 1)) (v : Tm 0)
  : (Tm.bv (k := (k + 1)) i).lst v = i.lastCases (v.castLE (by omega)) .bv
  := by simp [lst]

@[simp]
theorem Tm.lst_univ {k : ℕ} (ℓ : ℕ) (v : Tm 0)
  : (Tm.univ (k := (k + 1)) ℓ).lst v = .univ ℓ
  := by simp [lst]

@[simp]
theorem Tm.lst_empty {k : ℕ} (v : Tm 0) : (Tm.empty (k := (k + 1))).lst v = .empty
  := by simp [lst]

@[simp]
theorem Tm.lst_unit {k : ℕ} (v : Tm 0) : (Tm.unit (k := (k + 1))).lst v = .unit
  := by simp [lst]

@[simp]
theorem Tm.lst_null {k : ℕ} (v : Tm 0) : (Tm.null (k := (k + 1))).lst v = .null
  := by simp [lst]

@[simp]
theorem Tm.lst_eqn {k : ℕ} (a b : Tm (k + 1)) (v : Tm 0)
  : (Tm.eqn (k := (k + 1)) a b).lst v = .eqn (a.lst v) (b.lst v)
  := by simp [lst]

@[simp]
theorem Tm.lst_pi {k : ℕ} (A : Tm (k + 1)) (B : Tm (k + 2)) (v : Tm 0)
  : (Tm.pi (k := (k + 1)) A B).lst v = .pi (A.lst v) (B.lst v)
  := by simp [lst]

@[simp]
theorem Tm.lst_sigma {k : ℕ} (A : Tm (k + 1)) (B : Tm (k + 2)) (v : Tm 0)
  : (Tm.sigma (k := (k + 1)) A B).lst v = .sigma (A.lst v) (B.lst v)
  := by simp [lst]

@[simp]
theorem Tm.lst_abs {k : ℕ} (A : Tm (k + 1)) (b : Tm (k + 2)) (v : Tm 0)
  : (Tm.abs (k := (k + 1)) A b).lst v = .abs (A.lst v) (b.lst v)
  := by simp [lst]

@[simp]
theorem Tm.lst_app {k : ℕ} (f a : Tm (k + 1)) (v : Tm 0)
  : (Tm.app (k := (k + 1)) f a).lst v = .app (f.lst v) (a.lst v)
  := by simp [lst]

@[simp]
theorem Tm.lst_pair {k : ℕ} (a b : Tm (k + 1)) (v : Tm 0)
  : (Tm.pair (k := (k + 1)) a b).lst v = .pair (a.lst v) (b.lst v)
  := by simp [lst]

@[simp]
theorem Tm.lst_fst {k : ℕ} (p : Tm (k + 1)) (v : Tm 0)
  : (Tm.fst (k := (k + 1)) p).lst v = .fst (p.lst v)
  := by simp [lst]

@[simp]
theorem Tm.lst_snd {k : ℕ} (p : Tm (k + 1)) (v : Tm 0)
  : (Tm.snd (k := (k + 1)) p).lst v = .snd (p.lst v)
  := by simp [lst]

@[simp]
theorem Tm.lst_dite {k : ℕ} (φ : Tm (k + 1)) (l r : Tm (k + 2)) (v : Tm 0)
  : (Tm.dite (k := (k + 1)) φ l r).lst v = .dite (φ.lst v) (l.lst v) (r.lst v)
  := by simp [lst]

@[simp]
theorem Tm.lst_trunc {k : ℕ} (A : Tm (k + 1)) (v : Tm 0)
  : (Tm.trunc (k := (k + 1)) A).lst v = .trunc (A.lst v)
  := by simp [lst]

@[simp]
theorem Tm.lst_choose {k : ℕ} (A : Tm (k + 1)) (φ : Tm (k + 2)) (v : Tm 0)
  : (Tm.choose (k := (k + 1)) A φ).lst v = .choose (A.lst v) (φ.lst v)
  := by simp [lst]

@[simp]
theorem Tm.lst_nats {k : ℕ} (v : Tm 0) : (Tm.nats (k := (k + 1))).lst v = .nats
  := by simp [lst]

@[simp]
theorem Tm.lst_zero {k : ℕ} (v : Tm 0) : (Tm.zero (k := (k + 1))).lst v = .zero
  := by simp [lst]

@[simp]
theorem Tm.lst_succ {k : ℕ} (n : Tm (k + 1)) (v : Tm 0)
  : (Tm.succ (k := (k + 1)) n).lst v = .succ (n.lst v)
  := by simp [lst]

@[simp]
theorem Tm.lst_natrec {k : ℕ} (C : Tm (k + 2)) (s : Tm (k + 2)) (z : Tm (k + 1)) (n : Tm (k + 1))
  (v : Tm 0) : (Tm.natrec (k := (k + 1)) C s z n).lst v =
  .natrec (C.lst v) (s.lst v) (z.lst v) (n.lst v) := by simp [lst]

@[simp]
theorem Tm.lst_has_ty {k : ℕ} (A a : Tm (k + 1)) (v : Tm 0)
  : (Tm.has_ty (k := (k + 1)) A a).lst v = .has_ty (A.lst v) (a.lst v)
  := by simp [lst]

@[simp]
theorem Tm.lst_invalid {k : ℕ} (v : Tm 0) : (Tm.invalid (k := (k + 1))).lst v = .invalid
  := by simp [lst]

def Tm.succIndOn {motive : ∀ k, Tm (k + 1) → Sort*}
  (fv : ∀ {k} (x : String), motive k (.fv x))
  (bv : ∀ {k} (i : Fin (k + 1)), motive k (.bv i))
  (univ : ∀ {k} (ℓ : ℕ), motive k (.univ ℓ))
  (empty : ∀ {k}, motive k .empty)
  (unit : ∀ {k}, motive k .unit)
  (null : ∀ {k}, motive k .null)
  (eqn : ∀ {k} (a b : Tm (k + 1)), motive k a → motive k b → motive k (.eqn a b))
  (pi : ∀ {k} (A : Tm (k + 1)) (B : Tm (k + 2)), motive k A → motive (k + 1) B → motive k (.pi A B))
  (sigma : ∀ {k} (A : Tm (k + 1)) (B : Tm (k + 2)),
    motive k A → motive (k + 1) B → motive k (.sigma A B))
  (abs : ∀ {k} (A : Tm (k + 1)) (b : Tm (k + 2)),
    motive k A → motive (k + 1) b → motive k (.abs A b))
  (app : ∀ {k} (f a : Tm (k + 1)), motive k f → motive k a → motive k (.app f a))
  (pair : ∀ {k} (a b : Tm (k + 1)),
    motive k a → motive k b → motive k (.pair a b))
  (fst : ∀ {k} (p : Tm (k + 1)), motive k p → motive k (.fst p))
  (snd : ∀ {k} (p : Tm (k + 1)), motive k p → motive k (.snd p))
  (dite : ∀ {k} (φ : Tm (k + 1)) (l r : Tm (k + 2)),
    motive k φ → motive (k + 1) l → motive (k + 1) r → motive k (.dite φ l r))
  (trunc : ∀ {k} (A : Tm (k + 1)), motive k A → motive k (.trunc A))
  (choose : ∀ {k} (A : Tm (k + 1)) (φ : Tm (k + 2)),
    motive k A → motive (k + 1) φ → motive k (.choose A φ))
  (nats : ∀ {k}, motive k .nats)
  (zero : ∀ {k}, motive k .zero)
  (succ : ∀ {k} (n : Tm (k + 1)), motive k n → motive k (.succ n))
  (natrec : ∀ {k} (C : Tm (k + 2)) (s : Tm (k + 2)) (z : Tm (k + 1)) (n : Tm (k + 1)),
    motive (k + 1) C → motive (k + 1) s → motive k z → motive k n → motive k (.natrec C s z n))
  (has_ty : ∀ {k} (A a : Tm (k + 1)), motive k A → motive k a → motive k (.has_ty A a))
  (invalid : ∀ {k}, motive k .invalid)
  {k : ℕ} (t : Tm (k + 1)) : motive k t
  := match t with
  | .fv x => fv x
  | .bv i => bv i
  | .univ ℓ => univ ℓ
  | .empty => empty
  | .unit => unit
  | .null => null
  | .eqn a b =>
    eqn a b
      (a.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (b.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .pi A B =>
    pi A B
      (A.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (B.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .sigma A B =>
    sigma A B
      (A.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (B.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .abs A b =>
    abs A b
      (A.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (b.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .app a b =>
    app a b
      (a.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (b.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .pair a b =>
    pair a b
      (a.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (b.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .fst p =>
    fst p
      (p.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .snd p =>
    snd p
      (p.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .dite φ l r =>
    dite φ l r
      (φ.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (l.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (r.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .trunc A =>
    trunc A
      (A.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .choose A φ =>
    choose A φ
      (A.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (φ.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .nats => nats
  | .zero => zero
  | .succ n => succ n
    (n.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
      nats zero succ natrec has_ty invalid)
  | .natrec C s z n =>
    natrec C s z n
      (C.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (s.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (z.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (n.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .has_ty A a =>
    has_ty A a
      (A.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (a.succIndOn fv bv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .invalid => invalid

theorem Tm.lst_of_fv {k : ℕ} (t : Tm (k + 1)) (x : String) : (t.lst (.fv x)) = t.open x
  := by induction t using succIndOn <;> simp [lst, Tm.open, castLE, *]

theorem Tm.lst_cast_succ {k : ℕ} (t : Tm k) (v : Tm 0)
  : (t.castLE (Nat.le_succ k)).lst v = t
  := by induction t with
  | bv i =>
    simp only [castLE, Nat.succ_eq_add_one, lst]
    exact i.lastCases_castSucc
      (motive := fun _ => Tm _)
      (last := v.castLE (by omega)) (cast := Tm.bv)
  | _ => simp [castLE, *]

@[simp]
theorem Tm.lst_castSucc {k : ℕ} (t : Tm k) (v : Tm 0)
  : t.castSucc.lst v = t := t.lst_cast_succ v

-- @[simp]
-- theorem Tm.lst_coe_succ {k : ℕ} (t : Tm k) (v : Tm 0)
--   : Tm.lst (t : Tm (k + 1)) v = t := t.lst_cast_succ v

@[simp]
theorem Tm.lst_castAdd_succ {k : ℕ} (n : ℕ) (t : Tm k) (v : Tm 0)
  : (t.castAdd (n + 1)).lst v = t.castAdd n
  := by rw [castAdd_succ, lst_castSucc]

@[simp]
theorem Tm.lst_cast_zero {k : ℕ} (t : Tm 0) (v : Tm 0)
  : (t.castLE (Nat.zero_le (k + 1))).lst v = t.castLE (Nat.zero_le k)
  := by rw [<-castLE_castLE (m := k), lst_cast_succ]

theorem Tm.open_cast_succ {k : ℕ} (t : Tm k) (x : String)
  : (t.castLE (Nat.le_succ k)).open x = t
  := by rw [<-lst_of_fv, lst_cast_succ]

@[simp]
theorem Tm.open_castSucc {k : ℕ} (t : Tm k) (x : String)
  : t.castSucc.open x = t := t.open_cast_succ x

theorem Tm.open_cast_lt {lo hi : ℕ} (h : lo < hi + 1) (t : Tm lo) (x : String)
  : (t.castLE (le_of_lt h)).open x = t.castLE (m := hi) (by omega)
  := by rw [<-castLE_castLE (m := hi), open_cast_succ]

@[simp]
theorem Tm.open_cast_zero {k : ℕ} (t : Tm 0) (x : String)
  : (t.castLE (Nat.zero_le (k + 1))).open x = t.castLE (Nat.zero_le k)
  := by rw [<-castLE_castLE (m := k), open_cast_succ]

-- @[simp]
-- theorem Tm.open_coe_succ {k : ℕ} (t : Tm k) (x : String)
--   : Tm.open (t : Tm (k + 1)) x = t := t.open_cast_succ x

@[simp]
theorem Tm.open_castAdd_succ {k : ℕ} (n : ℕ) (t : Tm k) (x : String)
  : (t.castAdd (n + 1)).open x = t.castAdd n
  := by rw [castAdd_succ, open_castSucc]

def Tm.close {k : ℕ} (t : Tm k) (x : String) : Tm (k + 1) := match t with
  | .fv y => if x = y then .bv (Fin.ofNat (k + 1) k) else .fv y
  | .bv i => .bv i.castSucc
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.close x) (b.close x)
  | .pi A B => .pi (A.close x) (B.close x)
  | .sigma A B => .sigma (A.close x) (B.close x)
  | .abs A b => .abs (A.close x) (b.close x)
  | .app f a => .app (f.close x) (a.close x)
  | .pair a b => .pair (a.close x) (b.close x)
  | .fst p => .fst (p.close x)
  | .snd p => .snd (p.close x)
  | .dite φ l r => .dite (φ.close x) (l.close x) (r.close x)
  | .trunc A => .trunc (A.close x)
  | .choose A φ => .choose (A.close x) (φ.close x)
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.close x)
  | .natrec C s z n => .natrec (C.close x) (s.close x) (z.close x) (n.close x)
  | .has_ty A a => .has_ty (A.close x) (a.close x)
  | .invalid => .invalid

theorem Tm.open_close {k : ℕ} (t : Tm k) (x : String) : (t.close x).open x = t
  := by induction t with
  | fv => simp only [close, Fin.ofNat_eq_cast, Fin.natCast_eq_last]; split <;> simp [Tm.open, *]
  | _ => simp [Tm.open, close, *]

@[simp]
def Tm.fvs {k : ℕ} : Tm k → Finset String
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

theorem Tm.close_open {k : ℕ} (t : Tm (k + 1)) (x : String) (h : x ∉ t.fvs)
  : (t.open x).close x = t := by induction t using succIndOn with
  | fv => convert h using 0; simp [close]
  | bv i => cases i using Fin.lastCases <;> simp [open_bv, close]
  | _ => simp at h; grind [Tm.open, close]

theorem Tm.fvs_open {k : ℕ} (t : Tm (k + 1)) (x : String) : (t.open x).fvs ⊆ insert x t.fvs
  := by induction t using succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp [«open»]
  | _ =>
    simp only [
      «open», fvs, Finset.union_subset_iff, Finset.subset_insert
    ] <;>
    (try constructorm* _ ∧ _) <;>
    apply Finset.Subset.trans (by assumption) <;>
    intro x <;> grind

theorem Tm.fvs_close {k : ℕ} (t : Tm k) (x : String) : (t.close x).fvs = t.fvs.erase x
  := by induction t with
  | fv => simp only [close]; split <;> simp [*]
  | _ => simp [close, Finset.erase_union_distrib, *]

theorem Tm.fvs_close_subset {k : ℕ} (t : Tm k) (x : String) : (t.close x).fvs ⊆ t.fvs
  := by simp only [fvs_close, Finset.erase_subset]

theorem Tm.fvs_close_notMem {k : ℕ} (t : Tm k) (x : String) : x ∉ (t.close x).fvs
  := by simp [fvs_close]

def Tm.lsv {k : ℕ} (t : Tm k) (x : String) (v : Tm 0) : Tm k := match t with
  | .fv y => if x = y then v.castLE (by omega) else .fv y
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

theorem Tm.lst_close {k : ℕ} (t : Tm k) (x : String) (v : Tm 0)
  : (t.close x).lst v = t.lsv x v
  := by induction t with
  | fv => simp only [close, lsv]; split <;> simp [lst]
  | _ => simp [close, lst, lsv, *]

theorem Tm.lsv_open {k : ℕ} (t : Tm (k + 1)) (x : String) (v : Tm 0) (hx : x ∉ t.fvs)
  : (t.open x).lsv x v = t.lst v
  := by induction t using succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp [lsv, lst, «open»]
  | _ =>
    simp at hx
    simp [lsv, *]

def Tm.VSubst : Type := String → Tm 0

instance Tm.VSubst.instOne : One VSubst where one := .fv

def Tm.VSubst.get {k : ℕ} (v : VSubst) (x : String) : Tm k := (v x).castLE (by omega)

@[simp]
theorem Tm.VSubst.get_one {k : ℕ} (x : String) : get (k := k) 1 x = .fv x := rfl

@[simp]
theorem Tm.VSubst.castLE_get {lo hi : ℕ} (h : lo ≤ hi) (v : VSubst) (x : String)
  : (v.get x).castLE h = v.get x
  := by simp [get]

def Tm.lset (t : Tm 0) (x : String) : VSubst := fun y => if x = y then t else .fv y

theorem Tm.get_lset {k} (t : Tm 0) (x y : String)
  : (t.lset x).get (k := k) y = if x = y then t.castLE (Nat.zero_le _) else .fv y
  := by simp only [lset, VSubst.get]; split <;> rfl

@[simp]
theorem Tm.get_lset_self {k} (t : Tm 0) (x : String)
  : (t.lset x).get (k := k) x = t.castLE (Nat.zero_le _)
  := by simp [Tm.get_lset]

def Tm.ls {k : ℕ} (t : Tm k) (v : VSubst) : Tm k := match t with
  | .fv y => v.get y
  | .bv i => .bv i
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn a b => .eqn (a.ls v) (b.ls v)
  | .pi A B => .pi (A.ls v) (B.ls v)
  | .sigma A B => .sigma (A.ls v) (B.ls v)
  | .abs A b => .abs (A.ls v) (b.ls v)
  | .app f a => .app (f.ls v) (a.ls v)
  | .pair a b => .pair (a.ls v) (b.ls v)
  | .fst p => .fst (p.ls v)
  | .snd p => .snd (p.ls v)
  | .dite φ l r => .dite (φ.ls v) (l.ls v) (r.ls v)
  | .trunc A => .trunc (A.ls v)
  | .choose A φ => .choose (A.ls v) (φ.ls v)
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.ls v)
  | .natrec C s z n => .natrec (C.ls v) (s.ls v) (z.ls v) (n.ls v)
  | .has_ty A a => .has_ty (A.ls v) (a.ls v)
  | .invalid => .invalid

instance Tm.instSMul {k} : SMul VSubst (Tm k) where
  smul v t := t.ls v

theorem Tm.smul_def {k} {v : VSubst} {t : Tm k} : v • t = t.ls v := rfl

@[simp]
theorem Tm.smul_fv {v : VSubst} {k x} : v • Tm.fv (k := k) x = v.get x := rfl

@[simp]
theorem Tm.smul_bv {v : VSubst} {k i} : v • Tm.bv (k := k) i = .bv i := rfl

@[simp]
theorem Tm.smul_univ {v : VSubst} {k ℓ} : v • Tm.univ (k := k) ℓ = .univ ℓ := rfl

@[simp]
theorem Tm.smul_empty {v : VSubst} {k} : v • Tm.empty (k := k) = .empty := rfl

@[simp]
theorem Tm.smul_unit {v : VSubst} {k} : v • Tm.unit (k := k) = .unit := rfl

@[simp]
theorem Tm.smul_null {v : VSubst} {k} : v • Tm.null (k := k) = .null := rfl

@[simp]
theorem Tm.smul_eqn {v : VSubst} {k a b}
  : v • Tm.eqn (k := k) a b = Tm.eqn (v • a) (v • b) := rfl

@[simp]
theorem Tm.smul_pi {v : VSubst} {k A B}
  : v • Tm.pi (k := k) A B = Tm.pi (v • A) (v • B) := rfl

@[simp]
theorem Tm.smul_sigma {v : VSubst} {k A B}
  : v • Tm.sigma (k := k) A B = Tm.sigma (v • A) (v • B) := rfl

@[simp]
theorem Tm.smul_abs {v : VSubst} {k A b}
  : v • Tm.abs (k := k) A b = Tm.abs (v • A) (v • b) := rfl

@[simp]
theorem Tm.smul_app {v : VSubst} {k f a}
  : v • Tm.app (k := k) f a = Tm.app (v • f) (v • a) := rfl

@[simp]
theorem Tm.smul_pair {v : VSubst} {k a b}
  : v • Tm.pair (k := k) a b = Tm.pair (v • a) (v • b) := rfl

@[simp]
theorem Tm.smul_fst {v : VSubst} {k p} : v • Tm.fst (k := k) p = Tm.fst (v • p) := rfl

@[simp]
theorem Tm.smul_snd {v : VSubst} {k p} : v • Tm.snd (k := k) p = Tm.snd (v • p) := rfl

@[simp]
theorem Tm.smul_dite {v : VSubst} {k φ l r}
  : v • Tm.dite (k := k) φ l r = Tm.dite (v • φ) (v • l) (v • r) := rfl

@[simp]
theorem Tm.smul_trunc {v : VSubst} {k A}
  : v • Tm.trunc (k := k) A = Tm.trunc (v • A) := rfl

@[simp]
theorem Tm.smul_choose {v : VSubst} {k A φ}
  : v • Tm.choose (k := k) A φ = Tm.choose (v • A) (v • φ) := rfl

@[simp]
theorem Tm.smul_nats {v : VSubst} {k} : v • Tm.nats (k := k) = .nats := rfl

@[simp]
theorem Tm.smul_zero {v : VSubst} {k} : v • Tm.zero (k := k) = .zero := rfl

@[simp]
theorem Tm.smul_succ {v : VSubst} {k n}
  : v • Tm.succ (k := k) n = Tm.succ (v • n) := rfl

@[simp]
theorem Tm.smul_natrec {v : VSubst} {k C s z n}
  : v • Tm.natrec (k := k) C s z n = Tm.natrec (v • C) (v • s) (v • z) (v • n) := rfl

@[simp]
theorem Tm.smul_has_ty {v : VSubst} {k A a}
  : v • Tm.has_ty (k := k) A a = Tm.has_ty (v • A) (v • a) := rfl

@[simp]
theorem Tm.smul_invalid {v : VSubst} {k} : v • Tm.invalid (k := k) = .invalid := rfl

theorem Tm.ls_one {k : ℕ} (t : Tm k) : (1 : VSubst) • t = t := by induction t <;> simp [*]

theorem Tm.ls_lset {k : ℕ} (t : Tm k) (x : String) (v : Tm 0) : (v.lset x) • t = t.lsv x v
  := by induction t <;> simp [lsv, Tm.get_lset, *]

theorem Tm.lsv_not_mem {k : ℕ} (t : Tm k) (x : String) (v : Tm 0) (hx : x ∉ t.fvs)
  : t.lsv x v = t := by induction t with
  | _ => simp at hx; simp [lsv, *]

theorem Tm.ls_lset_not_mem {k : ℕ} (t : Tm k) (x : String) (v : Tm 0) (hx : x ∉ t.fvs)
  : (v.lset x) • t = t
  := by rw [ls_lset, lsv_not_mem (hx := hx)]

instance Tm.VSubst.instMul : Mul VSubst where mul v₁ v₂ := fun x => v₁ • (v₂.get x)

theorem Tm.castLE_ls {lo hi : ℕ} (h : lo ≤ hi) (t : Tm lo) (v : VSubst)
  : (v • t).castLE h = v • t.castLE h
  := by induction t generalizing hi <;> simp [castLE, *]

@[simp]
theorem Tm.VSubst.get_mul {k} (v₁ v₂ : VSubst) (x : String)
  : (v₁ * v₂).get (k := k) x = v₁ • (v₂.get x)
  := by simp [HMul.hMul, Mul.mul, get, castLE_ls]

theorem Tm.ls_ls {k : ℕ} (t : Tm k) (v₁ v₂ : VSubst) : v₁ • (v₂ • t) = (v₁ * v₂) • t
  := by induction t <;> simp [*]

@[ext]
theorem Tm.VSubst.ext {v1 v2 : VSubst} (h : ∀ x, v1.get (k := 0) x = v2.get x) : v1 = v2
  := by funext x; convert h x using 1 <;> simp [get]

@[simp]
theorem Tm.lset_var (x : String) : (Tm.fv x).lset x = 1 := by ext y; simp [Tm.get_lset]

instance Tm.VSubst.instMonoid : Monoid VSubst where
  mul_assoc v₁ v₂ v₃ := by ext x; simp [Tm.ls_ls]
  one_mul v := by ext x; simp [ls_one]
  mul_one v := by ext x; simp

instance Tm.VSubst.instMulAction {k} : MulAction VSubst (Tm k) where
  one_smul t := t.ls_one
  mul_smul v v' t := by simp [ls_ls]

def Tm.VSubst.EqOn (L : Finset String) (v v' : Tm.VSubst) : Prop
  := ∀ x ∈ L, v.get (k := 0) x = v'.get x

theorem Tm.VSubst.get_k_cast (v : VSubst) (k : ℕ) (x : String)
  : v.get (k := k) x = (v.get (k := 0) x).castLE (Nat.zero_le _)
  := by simp [get]

theorem Tm.VSubst.EqOn.get {L v v'} (h : EqOn L v v') {k} (x : String) (hx : x ∈ L)
  : v.get (k := k) x = v'.get x := by simp only [get_k_cast _ k, h x hx]

theorem Tm.VSubst.EqOn.symm {L v v'} (h : EqOn L v v') : EqOn L v' v := fun x hx => (h x hx).symm

theorem Tm.VSubst.EqOn.anti {S L : Finset String} (h : S ⊆ L) {v v' : VSubst} (hv : v.EqOn L v')
  : v.EqOn S v' := fun x hx => hv x (h hx)

theorem Tm.ls_eqOn_fvs {k : ℕ} (t : Tm k) (v v' : VSubst) (h : v.EqOn t.fvs v')
  : v • t = v' • t := by
  induction t with
  | fv x => exact h.get x (by simp)
  | _ =>
    simp only [smul_def, ls]
    <;> congr 1 <;> apply_assumption
    <;> apply VSubst.EqOn.anti _ (by assumption)
    <;> intro x <;> grind [fvs]

theorem Tm.ls_eqOn_sub_fvs
  {L : Finset String} {k : ℕ} (t : Tm k) (v v' : VSubst) (h : v.EqOn L v') (hL : t.fvs ⊆ L)
  : v • t = v' • t := t.ls_eqOn_fvs v v' (h.anti hL)

def Tm.VSubst.IdAt (v : VSubst) (x : String) : Prop := v.get (k := 0) x = .fv x

theorem Tm.VSubst.IdAt.get {k v x} (h : IdAt v x) : v.get (k := k) x = .fv x
  := by rw [VSubst.get_k_cast, h]; rfl

def Tm.VSubst.Clamped (L : Finset String) (v : VSubst) : Prop := ∀ x ∉ L, v.IdAt x

theorem Tm.VSubst.Clamped.get {L v} (h : Clamped L v) {k} (x : String) (hx : x ∉ L)
  : v.get (k := k) x = .fv x := (h x hx).get

@[simp]
theorem Tm.VSubst.open_get {k : ℕ} (v : VSubst) (x y : String)
  : (v.get (k := k + 1) x).open y = v.get x
  := by
  rw [get_k_cast (k := k + 1)]
  convert (v.get x).open_cast_succ (k := k) y using 2
  rw [get_k_cast (k := k), castLE_castLE]

@[simp]
theorem Tm.VSubst.lst_get {k : ℕ} (v : VSubst) (x : String) (t : Tm 0)
  : (v.get (k := k + 1) x).lst t = v.get x
  := by
  rw [get_k_cast (k := k + 1)]
  convert (v.get x).lst_cast_succ (k := k) t using 2
  rw [get_k_cast (k := k), castLE_castLE]

theorem Tm.castLE_lst {n m : ℕ} (h : n ≤ m) (t : Tm n) (v : VSubst)
  : (v • t).castLE h = v • t.castLE h
  := by induction t generalizing m <;> simp [castLE, *]

theorem Tm.ls_lst {k : ℕ} (t : Tm (k + 1)) (v : VSubst) (u : Tm 0)
  : v • (t.lst u) = (v • t).lst (v • u)
  :=  by induction t using succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp [lst, castLE_lst]
  | _ => simp [*]

theorem Tm.ls_lst_null {k : ℕ} (t : Tm (k + 1)) (v : VSubst)
  : v • (t.lst .null) = (v • t).lst .null
  := by simp [ls_lst]

theorem Tm.ls_open {k : ℕ} (t : Tm (k + 1)) (v : VSubst) (x : String)
  : v • (t.open x) = (v • t).lst (v.get x)
  := by rw [<-lst_of_fv, ls_lst]; rfl

def Tm.VSubst.set (v : VSubst) (x : String) (t : Tm 0) : VSubst
  := fun y => if y = x then t else v.get y

theorem Tm.VSubst.get_set {k v x t y} :
  (set v x t).get (k := k) y = if y = x then t.castLE (Nat.zero_le _) else v.get y
  := by simp only [set, get]; split <;> simp

def Tm.VSubst.lift (v : VSubst) (x : String) : VSubst := v.set x (.fv x)

theorem Tm.VSubst.get_lift {k v x y} :
  (lift v x).get (k := k) y = if y = x then .fv x else v.get y
  := by simp only [lift, get_set, castLE]

@[simp]
theorem Tm.VSubst.get_lift_same {k v x} :
  (lift v x).get (k := k) x = .fv x := by simp [get_lift]

theorem Tm.open_ls_id_at {k : ℕ} (t : Tm (k + 1))
  (v : VSubst) (x : String) (hx : v.IdAt x)
  : (v • t).open x = v • (t.open x)
  := by rw [ls_open, hx.get, lst_of_fv]

theorem Tm.open_ls_not_mem {k : ℕ} (t : Tm (k + 1))
  (v : VSubst) (x : String) (hx : x ∉ t.fvs)
  : (v • t).open x = (v.lift x) • (t.open x)
  := by
  rw [ls_open, VSubst.get_lift_same, lst_of_fv]
  congr 1
  apply Tm.ls_eqOn_fvs
  intro y hy
  rw [VSubst.get_lift]
  split
  case isTrue h => cases h; exact (hx hy).elim
  rfl

theorem Tm.open_ls_clamped {L : Finset String} {k : ℕ} (t : Tm (k + 1))
  (v : VSubst) (x : String) (hv : v.Clamped L) (hx : x ∉ L)
  : (v • t).open x = v • (t.open x)
  := t.open_ls_id_at v x (hv x hx)

theorem Tm.open_lsv_ne {k : ℕ} (t : Tm (k + 1))
  (v : Tm 0) (x y : String) (hx : x ≠ y)
  : (t.lsv x v).open y = (t.open y).lsv x v
  := by induction t using succIndOn with
  | fv =>
    simp only [lsv]
    split <;> simp [lsv, *]
  | bv i => cases i using Fin.lastCases <;> simp [lsv, «open», hx]
  | _ => simp [lsv, *]

theorem Tm.VSubst.Clamped.anti {S L : Finset String} (h : S ⊆ L) {v : VSubst} (hv : v.Clamped S)
  : v.Clamped L := fun x hx => hv x (Finset.not_mem_subset h hx)

def Tm.VSubst.clamp (L : Finset String) (v : VSubst) : VSubst :=
  fun x => if x ∈ L then v.get (k := 0) x else .fv x

theorem Tm.VSubst.get_clamp {L : Finset String} (v : VSubst) (k : ℕ) (x : String)
  : (v.clamp L).get (k := k) x = if x ∈ L then v.get x else .fv x
  := by simp only [get, clamp]; split <;> simp [castLE]

theorem Tm.VSubst.get_clamp_mem {L : Finset String} (v : VSubst) {k : ℕ} {x : String} (hx : x ∈ L)
  : (v.clamp L).get (k := k) x = v.get x
  := by simp [get_clamp, hx]

theorem Tm.VSubst.get_clamp_notMem
  {L : Finset String} (v : VSubst) {k : ℕ} {x : String} (hx : x ∉ L)
  : (v.clamp L).get (k := k) x = .fv x
  := by simp [get_clamp, hx]

@[simp]
theorem Tm.VSubst.id_at (L : Finset String) (v : VSubst) {x} (hx : x ∉ L)
  : (v.clamp L).IdAt x := by simp [IdAt, get_clamp, hx]

@[simp]
theorem Tm.VSubst.clamped (L : Finset String) (v : VSubst) : (v.clamp L).Clamped L
  := by intro x hx; simp [hx]

theorem Tm.VSubst.clamped_sub {S L : Finset String} (hs : S ⊆ L) (v : VSubst)
  : (v.clamp S).Clamped L := (v.clamped S).anti hs

@[simp]
theorem Tm.VSubst.clamp_eqOn (L : Finset String) (v : VSubst) : (v.clamp L).EqOn L v := by
  intro x hx; simp [get_clamp, hx]

theorem Tm.VSubst.clamp_eqOn_sub {S L : Finset String} (hs : S ⊆ L) (v : VSubst)
  : (v.clamp L).EqOn S v := (v.clamp_eqOn L).anti hs

theorem Tm.ls_clamp_sub_fvs {k : ℕ} (t : Tm k) {L : Finset String} (hL : t.fvs ⊆ L) (v : VSubst)
  : (v.clamp L) • t = v • t
  := t.ls_eqOn_fvs _ _ ((v.clamp_eqOn L).anti hL)

theorem Tm.ls_clamp_fvs {k : ℕ} (t : Tm k) (v : VSubst) : (v.clamp t.fvs) • t = v • t
  := t.ls_clamp_sub_fvs (by rfl) v

-- def Tm.bwkn {k : ℕ} (n : ℕ) : Tm (k + n) → Tm (k + n + 1)
--   | .fv x => .fv x
--   | .bv i => (i.cast (Nat.add_comm k n)).addCases
--     (fun i => .bv (i.castLE (by omega)))
--     (fun i => .bv (i.addNat (n + 1)))
--   | .univ ℓ => .univ ℓ
--   | .empty => .empty
--   | .unit => .unit
--   | .null => .null
--   | .eqn a b => .eqn (a.bwkn n) (b.bwkn n)
--   | .pi A B => .pi (A.bwkn n) (B.bwkn (n + 1))
--   | .abs A b => .abs (A.bwkn n) (b.bwkn (n + 1))
--   | .app f a => .app (f.bwkn n) (a.bwkn n)
--   | .invalid => .invalid

def Tm.depth {k : ℕ} : Tm k → ℕ
  | .eqn a b => (a.depth ⊔ b.depth) + 1
  | .pi A B => (A.depth ⊔ B.depth) + 1
  | .sigma A B => (A.depth ⊔ B.depth) + 1
  | .abs A b => (A.depth ⊔ b.depth) + 1
  | .app f a => (f.depth ⊔ a.depth) + 1
  | .pair a b => (a.depth ⊔ b.depth) + 1
  | .fst p => p.depth + 1
  | .snd p => p.depth + 1
  | .dite φ l r => (φ.depth ⊔ l.depth ⊔ r.depth) + 1
  | .trunc A => A.depth + 1
  | .choose A φ => (A.depth ⊔ φ.depth) + 1
  | .zero => 0
  | .succ n => n.depth + 1
  | .natrec C z s n => (C.depth ⊔ z.depth ⊔ s.depth ⊔ n.depth) + 1
  | .has_ty A a => (A.depth ⊔ a.depth) + 1
  | _ => 0

@[simp]
theorem Tm.depth_open {k : ℕ} (t : Tm (k + 1)) (x : String) : (t.open x).depth = t.depth
  := by induction t using succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp [«open», depth]
  | _ => simp [depth, *]

@[simp]
theorem Tm.depth_close {k : ℕ} (t : Tm k) (x : String) : (t.close x).depth = t.depth
  := by induction t with
  | fv => simp only [close, depth]; split <;> rfl
  | _ => simp [close, depth, *]

@[simp]
theorem Tm.depth_castLE {n m : ℕ} (h : n ≤ m) (t : Tm n) : (t.castLE h).depth = t.depth
  := by induction t generalizing m <;> simp [castLE, depth, *]

@[simp]
theorem Tm.depth_castAdd {k : ℕ} (t : Tm k) (n : ℕ) : (t.castAdd n).depth = t.depth
  := t.depth_castLE _

@[simp]
theorem Tm.depth_castSucc {k : ℕ} (t : Tm k) : t.castSucc.depth = t.depth
  := t.depth_castLE _

theorem Tm.depth_lst_le {k : ℕ} (t : Tm (k + 1)) (v : Tm 0) : (t.lst v).depth ≤ t.depth + v.depth
  := by induction t using succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp [lst, depth]
  | _ => simp only [lst, depth]; omega

theorem Tm.le_depth_lst {k : ℕ} (t : Tm (k + 1)) (v : Tm 0)
  : t.depth ≤ (t.lst v).depth
  := by induction t using succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp [lst, depth]
  | _ => simp only [lst, depth]; omega

theorem Tm.depth_lsv_le {k : ℕ} (t : Tm k) (x : String) (v : Tm 0)
  : (t.lsv x v).depth ≤ t.depth + v.depth
  := by induction t with
  | fv => simp only [lsv, depth]; split <;> simp [depth]
  | _ => simp only [lsv, depth]; omega

theorem Tm.le_depth_lsv {k : ℕ} (t : Tm k) (x : String) (v : Tm 0)
  : t.depth ≤ (t.lsv x v).depth
  := by induction t with
  | fv => simp only [lsv, depth]; split <;> simp [depth]
  | _ => simp only [lsv, depth]; omega

def Tm.lcIndCof (L : Finset String)
  {motive : Tm 0 → Sort*}
  (fv : ∀ (x : String), motive (.fv x))
  (univ : ∀ (ℓ : ℕ), motive (.univ ℓ))
  (empty : motive .empty)
  (unit : motive .unit)
  (null : motive .null)
  (eqn : ∀ (a b : Tm 0), motive a → motive b → motive (.eqn a b))
  (pi : ∀ (A : Tm 0) (B : Tm 1), motive A → (∀ x ∉ L, motive (B.open x)) → motive (.pi A B))
  (sigma : ∀ (A : Tm 0) (B : Tm 1),
    motive A → (∀ x ∉ L, motive (B.open x)) → motive (.sigma A B))
  (abs : ∀ (A : Tm 0) (b : Tm 1), motive A →
    (∀ x ∉ L, motive (b.open x)) → motive (.abs A b))
  (app : ∀ (f a : Tm 0), motive f → motive a → motive (.app f a))
  (pair : ∀ (a b : Tm 0), motive a → motive b → motive (.pair a b))
  (fst : ∀ (p : Tm 0), motive p → motive (.fst p))
  (snd : ∀ (p : Tm 0), motive p → motive (.snd p))
  (dite : ∀ (φ : Tm 0) (l r : Tm 1), motive φ →
    (∀ x ∉ L, motive (l.open x)) → (∀ x ∉ L, motive (r.open x)) → motive (.dite φ l r))
  (trunc : ∀ (A : Tm 0), motive A → motive (.trunc A))
  (choose : ∀ (A : Tm 0) (φ : Tm 1), motive A →
    (∀ x ∉ L, motive (φ.open x)) → motive (.choose A φ))
  (nats : motive .nats)
  (zero : motive .zero)
  (succ : ∀ (n : Tm 0), motive n → motive (.succ n))
  (natrec : ∀ (C s : Tm 1) (z n : Tm 0),
    (∀ x ∉ L, motive (C.open x)) → (∀ x ∉ L, motive (s.open x)) → motive z → motive n →
    motive (.natrec C s z n))
  (has_ty : ∀ (A a : Tm 0), motive A → motive a → motive (.has_ty A a))
  (invalid : motive .invalid)
  (t : Tm 0) : motive t
  := match t with
  | .fv x => fv x
  | .univ ℓ => univ ℓ
  | .empty => empty
  | .unit => unit
  | .null => null
  | .eqn a b =>
    eqn a b
      (a.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (b.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .pi A B =>
    pi A B
      (A.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (fun x _ => (B.open x).lcIndCof L fv univ empty unit null eqn pi sigma abs app pair
        fst snd dite trunc choose nats zero succ natrec has_ty invalid)
  | .sigma A B =>
    sigma A B
      (A.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (fun x _ => (B.open x).lcIndCof L fv univ empty unit null eqn pi sigma abs app pair
        fst snd dite trunc choose nats zero succ natrec has_ty invalid)
  | .abs A b =>
    abs A b
      (A.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (fun x _ => (b.open x).lcIndCof L fv univ empty unit null eqn pi sigma abs app pair
        fst snd dite trunc choose nats zero succ natrec has_ty invalid)
  | .app a b =>
    app a b
      (a.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (b.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .pair a b =>
    pair a b
      (a.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (b.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .fst p =>
    fst p
      (p.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .snd p =>
    snd p
      (p.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .dite φ l r =>
    dite φ l r
      (φ.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (fun x _ => (l.open x).lcIndCof L fv univ empty unit null eqn pi sigma abs app pair
        fst snd dite trunc choose nats zero succ natrec has_ty invalid)
      (fun x _ => (r.open x).lcIndCof L fv univ empty unit null eqn pi sigma abs app pair
        fst snd dite trunc choose nats zero succ natrec has_ty invalid)
  | .trunc A =>
    trunc A
      (A.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .choose A φ =>
    choose A φ
      (A.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (fun x _ => (φ.open x).lcIndCof L fv univ empty unit null eqn pi sigma abs app pair
        fst snd dite trunc choose nats zero succ natrec has_ty invalid)
  | .nats => nats
  | .zero => zero
  | .succ n => succ n (n.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair
    fst snd dite trunc choose nats zero succ natrec has_ty invalid)
  | .natrec C s z n => natrec C s z n
    (fun x _ => (C.open x).lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst
      snd dite trunc choose nats zero succ natrec has_ty invalid)
    (fun x _ => (s.open x).lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst
      snd dite trunc choose nats zero succ natrec has_ty invalid)
    (z.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc
      choose nats zero succ natrec has_ty invalid)
    (n.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
      nats zero succ natrec has_ty invalid)
  | .has_ty A a => has_ty A a
    (A.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
      nats zero succ natrec has_ty invalid)
    (a.lcIndCof L fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
      nats zero succ natrec has_ty invalid)
  | .invalid => invalid
termination_by depth t
decreasing_by all_goals { simp only [Tm.depth, Tm.depth_open]; omega }

def Tm.lcIndFvs
  {motive : Tm 0 → Sort*}
  (fv : ∀ (x : String), motive (.fv x))
  (univ : ∀ (ℓ : ℕ), motive (.univ ℓ))
  (empty : motive .empty)
  (unit : motive .unit)
  (null : motive .null)
  (eqn : ∀ (a b : Tm 0), motive a → motive b → motive (.eqn a b))
  (pi : ∀ (A : Tm 0) (B : Tm 1), motive A → (∀ x ∉ B.fvs, motive (B.open x)) → motive (.pi A B))
  (sigma : ∀ (A : Tm 0) (B : Tm 1), motive A → (∀ x ∉ B.fvs, motive (B.open x)) →
    motive (.sigma A B))
  (abs : ∀ (A : Tm 0) (b : Tm 1), motive A →
    (∀ x ∉ b.fvs, motive (b.open x)) → motive (.abs A b))
  (app : ∀ (f a : Tm 0), motive f → motive a → motive (.app f a))
  (pair : ∀ (a b : Tm 0), motive a → motive b → motive (.pair a b))
  (fst : ∀ (p : Tm 0), motive p → motive (.fst p))
  (snd : ∀ (p : Tm 0), motive p → motive (.snd p))
  (dite : ∀ (φ : Tm 0) (l r : Tm 1), motive φ →
    (∀ x ∉ l.fvs, motive (l.open x)) → (∀ x ∉ r.fvs, motive (r.open x)) → motive (.dite φ l r))
  (trunc : ∀ (A : Tm 0), motive A → motive (.trunc A))
  (choose : ∀ (A : Tm 0) (φ : Tm 1), motive A →
    (∀ x ∉ φ.fvs, motive (φ.open x)) → motive (.choose A φ))
  (nats : motive .nats)
  (zero : motive .zero)
  (succ : ∀ (n : Tm 0), motive n → motive (.succ n))
  (natrec : ∀ (C s : Tm 1) (z n : Tm 0),
    (∀ x ∉ C.fvs, motive (C.open x)) → (∀ x ∉ s.fvs, motive (s.open x)) → motive z → motive n →
    motive (.natrec C s z n))
  (has_ty : ∀ (A a : Tm 0), motive A → motive a → motive (.has_ty A a))
  (invalid : motive .invalid)
  (t : Tm 0) : motive t
  := match t with
  | .fv x => fv x
  | .univ ℓ => univ ℓ
  | .empty => empty
  | .unit => unit
  | .null => null
  | .eqn a b =>
    eqn a b
      (a.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (b.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .pi A B =>
    pi A B
      (A.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (fun x _ => (B.open x).lcIndFvs fv univ empty unit null eqn pi sigma abs app pair
        fst snd dite trunc choose nats zero succ natrec has_ty invalid)
  | .sigma A B =>
    sigma A B
      (A.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (fun x _ => (B.open x).lcIndFvs fv univ empty unit null eqn pi sigma abs app pair
        fst snd dite trunc choose nats zero succ natrec has_ty invalid)
  | .abs A b =>
    abs A b
      (A.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (fun x _ => (b.open x).lcIndFvs fv univ empty unit null eqn pi sigma abs app pair
        fst snd dite trunc choose nats zero succ natrec has_ty invalid)
  | .app a b =>
    app a b
      (a.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (b.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair
        fst snd dite trunc choose nats zero succ natrec has_ty invalid)
  | .pair a b =>
    pair a b
      (a.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (b.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .fst p =>
    fst p
      (p.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .snd p =>
    snd p
      (p.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .dite φ l r =>
    dite φ l r
      (φ.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (fun x _ => (l.open x).lcIndFvs fv univ empty unit null eqn pi sigma abs app pair
        fst snd dite trunc choose nats zero succ natrec has_ty invalid)
      (fun x _ => (r.open x).lcIndFvs fv univ empty unit null eqn pi sigma abs app pair
        fst snd dite trunc choose nats zero succ natrec has_ty invalid)
  | .trunc A =>
    trunc A
      (A.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
  | .choose A φ =>
    choose A φ
      (A.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
        nats zero succ natrec has_ty invalid)
      (fun x _ => (φ.open x).lcIndFvs fv univ empty unit null eqn pi sigma abs app pair
        fst snd dite trunc choose nats zero succ natrec has_ty invalid)
  | .nats => nats
  | .zero => zero
  | .succ n => succ n (n.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair
    fst snd dite trunc choose nats zero succ natrec has_ty invalid)
  | .natrec C s z n => natrec C s z n
    (fun x _ => (C.open x).lcIndFvs fv univ empty unit null eqn pi sigma abs app pair
      fst snd dite trunc choose nats zero succ natrec has_ty invalid)
    (fun x _ => (s.open x).lcIndFvs fv univ empty unit null eqn pi sigma abs app pair
      fst snd dite trunc choose nats zero succ natrec has_ty invalid)
    (z.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
      nats zero succ natrec has_ty invalid)
    (n.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
      nats zero succ natrec has_ty invalid)
  | .has_ty A a => has_ty A a
    (A.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
      nats zero succ natrec has_ty invalid)
    (a.lcIndFvs fv univ empty unit null eqn pi sigma abs app pair fst snd dite trunc choose
      nats zero succ natrec has_ty invalid)
  | .invalid => invalid
termination_by depth t
decreasing_by all_goals { simp only [Tm.depth, Tm.depth_open]; omega }
