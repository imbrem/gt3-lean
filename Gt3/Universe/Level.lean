import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Lattice

namespace Gt3

inductive UExpr : Type where
  | uv : String → UExpr
  | max : UExpr → UExpr → UExpr
  | imax : UExpr → UExpr → UExpr
  | zero : UExpr
  | succ : UExpr → UExpr

def UValuation : Type := String → ℕ

def UValuation.get (v : UValuation) (u : String) : ℕ := v u

theorem UValuation.ext {v₁ v₂ : UValuation} (h : ∀ u, v₁.get u = v₂.get u) : v₁ = v₂ := funext h

@[simp]
def UExpr.eval (v : UValuation) : UExpr → ℕ
  | UExpr.uv n => v.get n
  | UExpr.max a b => (eval v a) ⊔ (eval v b)
  | UExpr.imax a b => Nat.imax (eval v a) (eval v b)
  | UExpr.zero => 0
  | UExpr.succ a => (eval v a) + 1

def UExpr.add (ℓ : UExpr) : ℕ → UExpr
  | 0 => ℓ
  | n + 1 => UExpr.succ (add ℓ n)

instance UExpr.instZero : Zero UExpr where
  zero := UExpr.zero

instance UExpr.instOne : One UExpr where
  one := UExpr.succ 0

instance UExpr.instHAdd : HAdd UExpr ℕ UExpr where
  hAdd ℓ n := ℓ.add n

theorem UExpr.add_def (ℓ : UExpr) (n : ℕ) : ℓ + n = ℓ.add n := rfl

@[simp] theorem UExpr.add_zero (ℓ : UExpr) : ℓ + 0 = ℓ := rfl

theorem UExpr.add_succ (ℓ : UExpr) (n : ℕ) : ℓ + (n + 1) = UExpr.succ (ℓ + n) := rfl

theorem UExpr.add_assoc (ℓ : UExpr) (m n : ℕ) : ℓ + (m + n) = (ℓ + m) + n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [<-Nat.add_assoc, add_succ, add_succ, ih]

instance UExpr.instPreorder : Preorder UExpr where
  le a b := ∀ v : UValuation, a.eval v ≤ b.eval v
  le_refl a := fun v => le_refl (a.eval v)
  le_trans a b c hab hbc := fun v => le_trans (hab v) (hbc v)

@[simp] theorem UExpr.zero_le (a : UExpr) : 0 ≤ a := fun v => Nat.zero_le (a.eval v)

@[simp] theorem UExpr.le_succ (a : UExpr) : a ≤ UExpr.succ a := fun v => Nat.le_succ (a.eval v)

@[simp] theorem UExpr.le_max_left (a b : UExpr) : a ≤ UExpr.max a b := fun _ => le_sup_left

@[simp] theorem UExpr.le_max_right (a b : UExpr) : b ≤ UExpr.max a b := fun _ => le_sup_right

theorem UExpr.max_le {a b c : UExpr} : a ≤ c → b ≤ c → UExpr.max a b ≤ c :=
  fun hac hbc v => sup_le (hac v) (hbc v)

instance UExpr.setoid : Setoid UExpr where
  r a b := ∀ v : UValuation, a.eval v = b.eval v
  iseqv := {
    refl := (fun _ _ => rfl),
    symm h := (fun v => (h v).symm),
    trans h h' := (fun v => (h v).trans (h' v))
  }

theorem UExpr.succ_equiv {a b : UExpr} (h : a ≈ b) : UExpr.succ a ≈ UExpr.succ b
  := fun v => by rw [UExpr.eval, UExpr.eval, h v]

theorem UExpr.le_of_equiv {a b : UExpr} (h : a ≈ b) : a ≤ b := fun v => (h v).le

theorem UExpr.equiv_antisymm {a b : UExpr} (h₁ : a ≤ b) (h₂ : b ≤ a) : a ≈ b
  := fun v => le_antisymm (h₁ v) (h₂ v)

theorem UExpr.max_equiv {a₁ a₂ b₁ b₂ : UExpr} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
  UExpr.max a₁ b₁ ≈ UExpr.max a₂ b₂ := fun v => by rw [UExpr.eval, UExpr.eval, ha v, hb v]

@[simp] theorem UExpr.one_le_add_one (ℓ : UExpr) : 1 ≤ ℓ + 1
  := fun v => by simp [eval, add_def, add]

def ULevel : Type := Quotient UExpr.setoid

def ULevel.eval (v : UValuation) (ℓ : ULevel) : ℕ
  := Quotient.liftOn ℓ (UExpr.eval v) (fun _ _ h => h v)

instance ULevel.instZero : Zero ULevel where
  zero := ⟦0⟧

def ULevel.succ (ℓ : ULevel) : ULevel := Quotient.map UExpr.succ (fun _ _ h => UExpr.succ_equiv h) ℓ

instance ULevel.instOne : One ULevel where
  one := succ 0

def ULevel.add (ℓ : ULevel) : ℕ → ULevel
  | 0 => ℓ
  | n + 1 => ULevel.succ (add ℓ n)

instance ULevel.instHAdd : HAdd ULevel ℕ ULevel where
  hAdd ℓ n := ℓ.add n

theorem ULevel.add_def (ℓ : ULevel) (n : ℕ) : ℓ + n = ℓ.add n := rfl

@[simp] theorem ULevel.add_zero (ℓ : ULevel) : ℓ + 0 = ℓ := rfl

theorem ULevel.add_succ (ℓ : ULevel) (n : ℕ) : ℓ + (n + 1) = ULevel.succ (ℓ + n) := rfl

theorem ULevel.add_assoc (ℓ : ULevel) (m n : ℕ) : ℓ + (m + n) = (ℓ + m) + n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [<-Nat.add_assoc, add_succ, add_succ, ih]

instance ULevel.instPartialOrder : PartialOrder ULevel where
  le a b := Quotient.liftOn₂ a b
    (fun a b => a ≤ b)
    (fun _ _ _ _ h₁ h₂ => propext ⟨
      fun h => le_trans (UExpr.le_of_equiv (Setoid.symm h₁)) (le_trans h (UExpr.le_of_equiv h₂)),
      fun h => le_trans (UExpr.le_of_equiv h₁) (le_trans h (UExpr.le_of_equiv (Setoid.symm h₂)))⟩)
  le_refl a := by cases a using Quotient.inductionOn; simp
  le_trans a b c hab hbc := by cases a, b, c using Quotient.inductionOn₃; exact le_trans hab hbc
  le_antisymm a b h₁ h₂ := by
    cases a, b using Quotient.inductionOn₂; apply Quotient.sound (UExpr.equiv_antisymm h₁ h₂)

theorem ULevel.quot_le {a b : UExpr} (h : a ≤ b) : LE.le (α := ULevel) ⟦a⟧ ⟦b⟧ := h

@[simp]
theorem ULevel.zero_le (ℓ : ULevel) : 0 ≤ ℓ
  := by cases ℓ using Quotient.inductionOn; exact UExpr.zero_le _

@[simp]
theorem ULevel.le_succ (ℓ : ULevel) : ℓ ≤ ℓ.succ
  := by cases ℓ using Quotient.inductionOn; exact UExpr.le_succ _

instance ULevel.instSemilatticeSup : SemilatticeSup ULevel where
  sup a b := Quotient.liftOn₂ a b
    (fun a b => ⟦UExpr.max a b⟧)
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (UExpr.max_equiv h₁ h₂))
  le_sup_left a b := by cases a, b using Quotient.inductionOn₂; apply UExpr.le_max_left
  le_sup_right a b := by cases a, b using Quotient.inductionOn₂; apply UExpr.le_max_right
  sup_le a b c := by cases a, b, c using Quotient.inductionOn₃; apply UExpr.max_le

def ULevel.imax (a b : ULevel) : ULevel :=
  Quotient.liftOn₂ a b
    (fun a b => ⟦UExpr.imax a b⟧)
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (fun v => by rw [UExpr.eval, UExpr.eval, h₁ v, h₂ v]))

@[simp]
theorem ULevel.imax_self (ℓ : ULevel) : ℓ.imax ℓ = ℓ := by
  cases ℓ using Quotient.inductionOn; apply Quotient.sound
  intro v; simp [Nat.imax]; intro h; rw [h]

@[simp]
theorem ULevel.one_le_add_one (ℓ : ULevel) : 1 ≤ ℓ + 1 := by
  induction ℓ using Quotient.inductionOn; exact UExpr.one_le_add_one _

@[simp]
theorem ULevel.le_add (ℓ : ULevel) (n : ℕ) : ℓ ≤ ℓ + n := by induction n with
  | zero => exact le_refl ℓ
  | succ n ih => rw [add_succ]; exact le_trans ih (le_succ _)

abbrev UExpr.q (ℓ : UExpr) : ULevel := ⟦ℓ⟧

def ULevel.uv (u : String) : ULevel := (UExpr.uv u).q

@[simp]
theorem UExpr.q_uv (u : String) : (UExpr.uv u).q = ULevel.uv u := rfl

@[simp]
theorem UExpr.q_max (a b : UExpr) : (UExpr.max a b).q = a.q ⊔ b.q := rfl

@[simp]
theorem UExpr.q_imax (a b : UExpr) : (UExpr.imax a b).q = a.q.imax b.q := rfl

@[simp]
theorem UExpr.q_zero : (0 : UExpr).q = 0 := rfl

@[simp]
theorem UExpr.q_zero' : (UExpr.zero).q = 0 := rfl

@[simp]
theorem UExpr.q_succ (a : UExpr) : (UExpr.succ a).q = (a.q).succ := rfl

@[simp]
theorem UExpr.q_add (a : UExpr) (n : ℕ) : (a + n).q = (a.q) + n := by
  induction n <;> simp [UExpr.add_succ, UExpr.q_succ, ULevel.add_succ, *]

@[simp]
theorem ULevel.eval_q (v : UValuation) (a : UExpr) : (a.q).eval v = a.eval v := rfl

@[simp]
theorem ULevel.eval_uv (v : UValuation) (u : String) : (ULevel.uv u).eval v = v.get u := rfl

@[simp]
theorem ULevel.eval_sup (v : UValuation) (a b : ULevel) :
  (a ⊔ b).eval v = a.eval v ⊔ b.eval v := by induction a, b using Quotient.inductionOn₂; rfl

@[simp]
theorem ULevel.eval_imax (v : UValuation) (a b : ULevel) :
  (a.imax b).eval v = Nat.imax (a.eval v) (b.eval v) := by
  induction a, b using Quotient.inductionOn₂; rfl

@[simp]
theorem ULevel.eval_zero (v : UValuation) : (0 : ULevel).eval v = 0 := rfl

@[simp]
theorem ULevel.eval_one (v : UValuation) : (1 : ULevel).eval v = 1 := rfl

@[simp]
theorem ULevel.eval_succ (v : UValuation) (ℓ : ULevel) :
  (ℓ.succ).eval v = (ℓ.eval v) + 1 := by induction ℓ using Quotient.inductionOn; rfl

@[simp]
theorem ULevel.eval_add (v : UValuation) (ℓ : ULevel) (n : ℕ) :
  (ℓ + n).eval v = (ℓ.eval v) + n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [add_succ, eval_succ, ih]; omega

theorem ULevel.le_iff {a b : ULevel} : a ≤ b ↔ ∀v, a.eval v ≤ b.eval v
  := by cases a, b using Quotient.inductionOn₂; rfl

theorem ULevel.eval_le_of_le {a b : ULevel} (h : a ≤ b) (v : UValuation) : a.eval v ≤ b.eval v
  := ULevel.le_iff.mp h v

theorem ULevel.le_of_eval_le {a b : ULevel} (h : ∀ v, a.eval v ≤ b.eval v) : a ≤ b
  := ULevel.le_iff.mpr h

theorem ULevel.eq_of_eval_eq {a b : ULevel} (h : ∀ v, a.eval v = b.eval v) : a = b
  := le_antisymm (ULevel.le_of_eval_le (fun v => (h v).le))
                 (ULevel.le_of_eval_le (fun v => (h v).ge))

end Gt3
