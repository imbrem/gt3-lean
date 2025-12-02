-- To add a new term former; follow the instructions in `TERM_FORMER_CHECKLIST.md`
import Gt3.Syntax.Basic

namespace Gt3

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
  (univ : ∀ (ℓ : ULevel), motive (.univ ℓ))
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
  (univ : ∀ (ℓ : ULevel), motive (.univ ℓ))
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

end Gt3
