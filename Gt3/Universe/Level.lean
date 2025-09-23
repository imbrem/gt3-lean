import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Lattice

structure ULevel : Type where
  (lvl : ℕ)

instance ULevel.instZero : Zero ULevel where
  zero := ⟨0⟩

def ULevel.succ (ℓ : ULevel) : ULevel := ⟨ℓ.lvl + 1⟩

instance ULevel.instOne : One ULevel where
  one := succ 0

instance ULevel.instPartialOrder : PartialOrder ULevel where
  le a b := a.lvl ≤ b.lvl
  le_refl a := le_refl a.lvl
  le_trans a b c hab hbc := le_trans hab hbc
  le_antisymm a b h₁ h₂ := by cases a; cases b; cases le_antisymm (α := ℕ) h₁ h₂; rfl

@[simp] theorem ULevel.zero_le (ℓ : ULevel) : 0 ≤ ℓ := Nat.zero_le ℓ.lvl

@[simp] theorem ULevel.le_succ (ℓ : ULevel) : ℓ ≤ ℓ.succ := Nat.le_succ ℓ.lvl

instance ULevel.instSemilatticeSup : SemilatticeSup ULevel where
  sup a b := ⟨max a.lvl b.lvl⟩
  le_sup_left a b := le_max_left a.lvl b.lvl
  le_sup_right a b := le_max_right a.lvl b.lvl
  sup_le _ _ _ hac hbc := sup_le (α := ℕ) hac hbc

instance ULevel.instHAdd : HAdd ULevel ℕ ULevel where
  hAdd ℓ n := succ^[n] ℓ

@[simp] theorem ULevel.add_zero (ℓ : ULevel) : ℓ + 0 = ℓ := rfl

theorem ULevel.add_def (ℓ : ULevel) (n : ℕ) : ℓ + n = succ^[n] ℓ := by rfl

theorem ULevel.add_succ (ℓ : ULevel) (n : ℕ) : ℓ + (n + 1) = (ℓ + n).succ := by
  rw [add_def, Function.iterate_succ_apply']; rfl

@[simp]
theorem ULevel.one_le_add_one (ℓ : ULevel) : 1 ≤ ℓ + 1 := Nat.succ_le_succ (Nat.zero_le ℓ.lvl)

@[simp]
theorem ULevel.le_add (ℓ : ULevel) (n : ℕ) : ℓ ≤ ℓ + n := by induction n with
  | zero => exact le_refl ℓ
  | succ n ih => rw [add_succ]; exact le_trans ih (le_succ _)
