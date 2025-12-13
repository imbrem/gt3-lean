import Mathlib.Data.Erased
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Lattice.Fold

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Algebra.Ring.BooleanRing

namespace Gt3

open OmegaCompletePartialOrder

class Truthy (α : Type _) where
  truthy : α → Prop
  falsy : α → Prop
  consistent : ∀ a : α, ¬ (truthy a ∧ falsy a)

attribute [simp] Truthy.consistent

abbrev DecidableTruthy (α : Type _) [Truthy α] := ∀ a : α, Decidable (Truthy.truthy a)

abbrev DecidableFalsy (α : Type _) [Truthy α] := ∀ a : α, Decidable (Truthy.falsy a)

namespace Truthy

variable {α : Type _} [Truthy α]

abbrev boolean (a : α) : Prop := truthy a ∨ falsy a

theorem truthy_imp_boolean {a : α} : truthy a → boolean a := Or.inl

theorem falsy_imp_boolean {a : α} : falsy a → boolean a := Or.inr

abbrev undef (a : α) : Prop := ¬ boolean a

end Truthy

abbrev DecidableBoolean (α : Type _) [Truthy α] := ∀ a : α, Decidable (Truthy.boolean a)

class DecidableTruthiness (α : Type _) [Truthy α] where
  truthyDecidable : DecidableTruthy α
  falsyDecidable : DecidableFalsy α

open Truthy

class HasTruthy (α) [Truthy α] where
  tt : α
  tt_truthy : truthy (α := α) tt

class HasFalsy (α) [Truthy α] where
  ff : α
  ff_falsy : falsy (α := α) ff

class HasUndef (α) [Truthy α] where
  nab : α
  nab_undef : undef nab

class OneTruthy (α : Type _) [Truthy α] [One α] where
  one_truthy : truthy (α := α) 1

class ZeroFalsy (α : Type _) [Truthy α] [Zero α] where
  zero_falsy : falsy (α := α) 0

class TopTruthy (α : Type _) [Truthy α] [Top α] where
  top_truthy : truthy (α := α) ⊤

class BotFalsy (α : Type _) [Truthy α] [Bot α] where
  bot_falsy : falsy (α := α) ⊥

attribute [simp] OneTruthy.one_truthy ZeroFalsy.zero_falsy TopTruthy.top_truthy BotFalsy.bot_falsy

attribute [instance] DecidableTruthiness.truthyDecidable

attribute [instance] DecidableTruthiness.falsyDecidable

instance DecidableTruthiness.ofDecidable {α : Type _} [Truthy α]
  [htrue : DecidableTruthy α] [hfalse : DecidableFalsy α] : DecidableTruthiness α where
  truthyDecidable := htrue
  falsyDecidable := hfalse

namespace Truthy

variable {α} [Truthy α]

instance instProp : Truthy Prop where
  truthy p := p
  falsy p := ¬ p
  consistent p := by simp

@[simp] theorem truthy_id_prop (φ : Prop) : truthy (α := Prop) φ = φ := rfl

@[simp] theorem falsy_not_prop (φ : Prop) : falsy (α := Prop) φ = ¬ φ := rfl

instance instBool : Truthy Bool where
  truthy b := b = true
  falsy b := b = false
  consistent b := by simp

@[simp] theorem truthy_id_bool (b : Bool) : truthy (α := Bool) b = b
  := by cases b <;> rfl

@[simp] theorem falsy_not_bool (b : Bool) : falsy (α := Bool) b = ¬ b
  := by cases b <;> simp [falsy]

instance instNat : Truthy ℕ where
  truthy n := n ≠ 0
  falsy n := n = 0
  consistent n := by simp

theorem truthy_nat (n : ℕ) : truthy (α := ℕ) n = (n ≠ 0) := by rfl

theorem falsy_nat (n : ℕ) : falsy (α := ℕ) n = (n = 0) := by rfl

@[simp] theorem truthy_succ_nat (n : ℕ) : truthy (α := ℕ) (n + 1) := by simp [truthy]

instance instEmpty : Truthy Empty where
  truthy e := False
  falsy e := False
  consistent e := by simp

instance instUnit : Truthy Unit where
  truthy _ := True
  falsy _ := False
  consistent _ := by simp

@[simp] theorem truthy_unit (u : Unit) : truthy (α := Unit) u = True := rfl

end Truthy

instance HasTruthy.instProp : HasTruthy Prop where
  tt := True
  tt_truthy := by trivial

instance HasFalsy.instProp : HasFalsy Prop where
  ff := False
  ff_falsy := by simp

instance HasTruthy.instBool : HasTruthy Bool where
  tt := true
  tt_truthy := rfl

instance HasFalsy.instBool : HasFalsy Bool where
  ff := false
  ff_falsy := rfl

instance HasTruthy.instNat : HasTruthy ℕ where
  tt := 1
  tt_truthy := by simp [truthy]

instance HasFalsy.instNat : HasFalsy ℕ where
  ff := 0
  ff_falsy := by simp [falsy]

instance OneTruthy.instBool : OneTruthy Bool where
  one_truthy := rfl

instance ZeroFalsy.instBool : ZeroFalsy Bool where
  zero_falsy := rfl

instance OneTruthy.instNat : OneTruthy ℕ where
  one_truthy := by simp [truthy]

instance ZeroFalsy.instNat : ZeroFalsy ℕ where
  zero_falsy := by simp [falsy]

instance TopTruthy.instProp : TopTruthy Prop where
  top_truthy := by trivial

instance BotFalsy.instProp : BotFalsy Prop where
  bot_falsy := by simp

instance TopTruthy.instBool : TopTruthy Bool where
  top_truthy := rfl

instance BotFalsy.instBool : BotFalsy Bool where
  bot_falsy := rfl

instance BotFalsy.instNat : BotFalsy ℕ where
  bot_falsy := by simp [falsy]

class TruthySubsingleton (α : Type _) [Truthy α] where
  allEq_truthy : ∀ {a b : α}, truthy a → truthy b → a = b

class FalsySubsingleton (α : Type _) [Truthy α] where
  allEq_falsy : ∀ {a b : α}, falsy a → falsy b → a = b

class BooleanSubsingleton (α) [Truthy α] extends TruthySubsingleton α, FalsySubsingleton α where
  allEq_boolean : ∀ {a b : α}, boolean a → boolean b → a = b
  allEq_truthy h h' := allEq_boolean (Or.inl h) (Or.inl h')
  allEq_falsy h h' := allEq_boolean (Or.inr h) (Or.inr h')

instance TruthySubsingleton.instProp : TruthySubsingleton Prop where
  allEq_truthy a b := by simp only [truthy] at *; simp only [*]

instance TruthySubsingleton.instBool : TruthySubsingleton Bool where
  allEq_truthy h1 h2 := by cases h1; cases h2; rfl

instance FalsySubsingleton.instProp : FalsySubsingleton Prop where
  allEq_falsy h1 h2 := by simp only [falsy] at *; simp only [*]

instance FalsySubsingleton.instBool : FalsySubsingleton Bool where
  allEq_falsy h1 h2 := by cases h1; cases h2; rfl

instance FalsySubsingleton.instNat : FalsySubsingleton ℕ where
  allEq_falsy h1 h2 := by cases h1; cases h2; rfl

instance BooleanSubsingleton.instEmpty : BooleanSubsingleton Empty where
  allEq_boolean _ _ := by contradiction

instance BooleanSubsingleton.instUnit : BooleanSubsingleton Unit where
  allEq_boolean _ _ := rfl

class UndefSubsingleton (α) [Truthy α] where
  allEq_undef : ∀ {a b : α}, undef a → undef b → a = b

namespace Truthy

variable {α : Type _} [Truthy α]

class Boolean (α : Type _) [Truthy α] extends UndefSubsingleton α where
  truthy_or_falsy : ∀ a : α, truthy a ∨ falsy a
  allEq_undef h := (h (truthy_or_falsy _)).elim

attribute [simp] Boolean.truthy_or_falsy

namespace Boolean

variable [Boolean α]

@[simp]
theorem falsy_or_truthy (a : α) :
    falsy a ∨ truthy a := (truthy_or_falsy a).symm

@[simp]
theorem not_truthy_iff (a : α) :
    ¬truthy a ↔ falsy a := by
      cases truthy_or_falsy a
      <;> simp only [not_true_eq_false, false_iff, iff_true, *]
      <;> intro h
      <;> apply consistent a
      <;> simp only [and_self, *]

@[simp]
theorem not_falsy_iff (a : α) :
    ¬falsy a ↔ truthy a := by rw [<-not_truthy_iff]; apply not_not

theorem not_undef (a : α) : ¬undef a := by simp

instance decidableBoolean : DecidableBoolean α
  := fun _ => Decidable.isTrue (by simp)

instance instProp : Boolean Prop where
  truthy_or_falsy p := by by_cases p <;> simp [*]

instance instBool : Boolean Bool where
  truthy_or_falsy p := by cases p <;> simp

instance instNat : Boolean ℕ where
  truthy_or_falsy n := by cases n <;> simp

instance instEmpty : Boolean Empty where
  truthy_or_falsy e := by contradiction

instance instUnit : Boolean Unit where
  truthy_or_falsy _ := Or.inl trivial

end Boolean

end Truthy

inductive Fail (μ : Type _) (α : Type _) where
  | ans (ans : α) : Fail μ α
  | fail (e : μ) : Fail μ α
  deriving DecidableEq

namespace Fail

variable {μ}

instance instMonad : Monad (Fail μ) where
  pure := .ans
  bind
    | .ans a, f => f a
    | .fail e, _ => .fail e

instance instLawfulMonad : LawfulMonad (Fail μ)
  := LawfulMonad.mk'
    (id_map := fun x => by cases x <;> rfl)
    (pure_bind := fun x _ => rfl) (bind_assoc := fun x f g => by cases x <;> rfl)

variable {α}

instance instInhabited [Inhabited μ] : Inhabited (Fail μ α) where
  default := .fail default

instance instAnsInhabited [Inhabited α] : Inhabited (Fail μ α) where
  default := .ans default

instance instBot [Bot μ] : Bot (Fail μ α) where
  bot := .fail ⊥

variable [Truthy α]

instance instTruthy : Truthy (Fail μ α) where
  truthy
    | .ans a => truthy a
    | .fail _ => False
  falsy
    | .ans a => falsy a
    | .fail _ => False
  consistent
    | .ans a => consistent a
    | .fail _ => by simp

@[simp] theorem truthy_ans {a : α} : truthy (ans (μ := μ) a) = truthy a := rfl

@[simp] theorem falsy_ans {a : α} : falsy (ans (μ := μ) a) = falsy a := rfl

@[simp] theorem truthy_maybe {e : μ} : truthy (fail (α := α) e) = False := rfl

@[simp] theorem falsy_maybe {e : μ} : falsy (fail (α := α) e) = False := rfl

@[simp] theorem boolean_ans {a : α} : Truthy.boolean (ans (μ := μ) a) = Truthy.boolean a := by
  simp [Truthy.boolean]

@[simp] theorem boolean_maybe {e : μ} : Truthy.boolean (fail (α := α) e) = False := by
  simp [Truthy.boolean]

theorem undef_ans {a : α} : Truthy.undef (ans (μ := μ) a) = Truthy.undef a := by simp

theorem undef_maybe {e : μ} : Truthy.undef (fail (α := α) e) = True := by simp

instance instTruthySubsingleton [h : TruthySubsingleton α] : TruthySubsingleton (Fail μ α) where
  allEq_truthy {a b} := by
    cases a <;> cases b <;>
    simp only [truthy_ans, truthy_maybe, ans.injEq, false_imp_iff, imp_true_iff]
    apply h.allEq_truthy

instance instFalsySubsingleton [h : FalsySubsingleton α] : FalsySubsingleton (Fail μ α) where
  allEq_falsy {a b} := by
    cases a <;> cases b <;>
    simp only [falsy_ans, falsy_maybe, ans.injEq, false_imp_iff, imp_true_iff]
    apply h.allEq_falsy

instance instBooleanSubsingleton [h : BooleanSubsingleton α] : BooleanSubsingleton (Fail μ α) where
  allEq_boolean {a b} := by
    cases a <;> cases b <;>
    simp only [boolean_ans, boolean_maybe, ans.injEq, false_imp_iff, imp_true_iff]
    apply h.allEq_boolean

instance instUndefSubsingleton [Boolean α] [Subsingleton μ] : UndefSubsingleton (Fail μ α) where
  allEq_undef {a b} := by
    cases a <;> cases b <;>
    simp only [undef_ans, undef_maybe, Boolean.not_undef, fail.injEq, false_imp_iff, true_imp_iff]
    apply Subsingleton.elim

end Fail

def Done (α : Type _) (μ : Type _) := Fail μ α

def Fail.done {μ α} (a : Fail μ α) : Done α μ := a

def Done.fail {α μ} (a : Done α μ) : Fail μ α := a

@[simp] theorem Fail.fail_done {μ α} {a : Fail μ α} : Done.fail (μ := μ) a.done = a := rfl

@[simp] theorem Done.done_fail {α μ} {a : Done α μ} : Fail.done (α := α) a.fail = a := rfl

namespace Done

variable {α μ}

@[match_pattern]
def done (a : α) := Fail.ans (μ := μ) (α := α) a

@[match_pattern]
def hole (e : μ) := Fail.fail (μ := μ) (α := α) e

@[simp] theorem fail_done {a : α} : fail (μ := μ) (done a) = Fail.ans a := rfl

@[simp] theorem fail_hole {e : μ} : fail (α := α) (hole e) = Fail.fail e := rfl

@[cases_eliminator, induction_eliminator]
def casesOn {motive : Done α μ → Sort _}
  (done : ∀ a : α, motive (done a))
  (hole : ∀ e : μ, motive (hole e))
  : ∀ d : Done α μ, motive d
  | .done a => done a
  | .hole e => hole e

end Done

namespace Fail

variable {μ α}

@[simp] theorem done_fail {e : μ} : done (α := α) (fail e) = Done.hole e := rfl

@[simp] theorem done_ans {a : α} : done (μ := μ) (ans a) = Done.done a := rfl

end Fail

namespace Done

variable {α}

instance instMonad : Monad (Done α) where
  pure := hole
  bind
    | .hole e, f => f e
    | .done a, _ => .done a

instance instLawfulMonad : LawfulMonad (Done α)
  := LawfulMonad.mk'
    (id_map := fun x => by cases x <;> rfl)
    (pure_bind := fun x _ => rfl) (bind_assoc := fun x f g => by cases x <;> rfl)

variable {μ}

instance instInhabited [Inhabited μ] : Inhabited (Done α μ) where
  default := .hole default

instance instDoneInhabited [Inhabited α] : Inhabited (Done α μ) where
  default := .done default

instance instBot [Bot μ] : Bot (Done α μ) where
  bot := .hole ⊥

end Done

/-

abbrev Tribool (μ : Type _ := Unit) := Maybe Bool μ

variable {α μ}

def Maybe.defined : Maybe α μ → Prop
  | .ans _ => True
  | .maybe _ => False

def Maybe.undef : Maybe α μ → Prop
  | .ans _ => False
  | .maybe _ => True

instance Maybe.instZeroAns [Zero α] : Zero (Maybe α μ) where
  zero := .ans 0

instance Maybe.instOneAns [One α] : One (Maybe α μ) where
  one := .ans 1

instance Maybe.instZeroProp : Zero (Maybe Prop μ) where
  zero := .ans False

instance Maybe.instOneProp : One (Maybe Prop μ) where
  one := .ans True

class Maybe.TrueAnswer (α : Type _) (μ : Type _) [Truthy (Maybe α μ)] extends One (Maybe α μ)
  where
  one_truthy : truthy (α := Maybe α μ) 1 := by simp

class Maybe.FalseAnswer (α : Type _) (μ : Type _) [Truthy (Maybe α μ)] extends Zero (Maybe α μ)
  where
  zero_falsy : falsy (α := Maybe α μ) 0 := by simp

class Maybe.TruthyAnswer (α : Type _) (μ : Type _) extends
  Truthy α μ, TrueAnswer α μ, FalseAnswer α μ where

instance Maybe.instBoolAnswer {α μ} [htrue : TrueAnswer α μ] [hfalse : FalseAnswer α μ]
  : Maybe.BoolAnswer α μ where
  zero_falsy := hfalse.zero_falsy

variable [Maybe.ZeroOneAns α μ]

abbrev Maybe.yes : Maybe α μ := 1

abbrev Maybe.no : Maybe α μ := 0

class Maybe.CasesYesNo [Zero (Maybe α μ)] [One (Maybe α μ)] (α : Type _) (μ : Type _) where
  casesZeroOne {motive : Maybe α μ → Sort _}
    (yes : motive .yes)
    (no : motive .no)
    (maybe : ∀ id, motive (.maybe id))
    : ∀ m : Maybe α μ, motive m

-- @[cases_eliminator, induction_eliminator]
-- def Maybe.casesOn' {motive : Maybe α → Sort _}
--   (yes : motive 1)
--   (no : motive 0)
--   (maybe : ∀ a, motive (.maybe a))
--   : ∀ m : Maybe α, motive m
--   | 1 => yes
--   | 0 => no
--   | .maybe a => maybe a

instance [Bot α] : Bot (Maybe α) where
  bot := .maybe ⊥

def Maybe.casesBot {motive : Maybe Unit → Sort _}
  (yes : motive 1)
  (no : motive 0)
  (maybe : motive ⊥)
  : ∀ m : Maybe Unit, motive m
  | 1 => yes
  | 0 => no
  | ⊥ => maybe


section LE

variable [LE α]

instance Maybe.instLE : LE (Maybe α) where
  le
    | 1, 1 => True
    | 0, 0 => True
    | .maybe _, 1 => True
    | .maybe _, 0 => True
    | .maybe a, .maybe b => a ≤ b
    | _, _ => False

@[simp]
theorem Maybe.le_yes_yes : (1 : Maybe α) ≤ 1 := by trivial

@[simp]
theorem Maybe.le_no_no : (0 : Maybe α) ≤ 0 := by trivial

@[simp]
theorem Maybe.le_maybe_yes {a : α} : (Maybe.maybe a ≤ 1) := by trivial

@[simp]
theorem Maybe.maybe_le_maybe_iff {a b : α} :
  (Maybe.maybe a ≤ Maybe.maybe b) ↔ (a ≤ b) := by rfl

@[simp]
theorem Maybe.not_le_yes_no : ¬ (1 : Maybe α) ≤ 0 := by simp [LE.le]

@[simp]
theorem Maybe.not_le_no_yes : ¬ (0 : Maybe α) ≤ 1 := by simp [LE.le]

end LE

instance Maybe.instPreorder [Preorder α] : Preorder (Maybe α) where
  le_refl a := by cases a <;> simp

instance Maybe.instPartialOrder [PartialOrder α] : PartialOrder (Maybe α) where
  le a b := sorry
  le_refl _ := Or.inl rfl
  le_trans _ _ _ h _ := by cases h <;> simp [*]
  le_antisymm _ _ h h' := by cases h <;> cases h' <;> subst_vars <;> rfl

instance Maybe.instBot : OrderBot Maybe where
  bot_le _ := Or.inr rfl

instance Maybe.instSemilatticeInf : SemilatticeInf Maybe where
  inf a b := if a = b then a else ⊥
  inf_le_left _ _ := by split <;> simp [*]
  inf_le_right _ _ := by split <;> simp [*]
  le_inf _ _ _ h1 h2 := by cases h1 <;> cases h2 <;> subst_vars <;> simp

@[simp] theorem Maybe.inf_yes_no : (1 : Maybe) ⊓ (0 : Maybe) = ⊥ := rfl

@[simp] theorem Maybe.inf_no_yes : (0 : Maybe) ⊓ (1 : Maybe) = ⊥ := rfl

def Maybe.truthy : InfHom Maybe Prop where
  toFun a := a = 1
  map_inf' a b := by cases a <;> cases b <;> simp

def Maybe.falsy : InfHom Maybe Prop where
  toFun a := a = 0
  map_inf' a b := by cases a <;> cases b <;> simp

@[simp] theorem Maybe.yes_truthy : truthy 1 := rfl

@[simp] theorem Maybe.no_not_truthy : ¬ truthy 0 := by simp [Maybe.truthy]

@[simp] theorem Maybe.maybe_not_truthy : ¬ truthy ⊥ := by simp [Maybe.truthy]

@[simp] theorem Maybe.no_falsy : falsy 0 := rfl

@[simp] theorem Maybe.yes_not_falsy : ¬ (falsy 1) := by simp [Maybe.falsy]

@[simp] theorem Maybe.maybe_not_falsy : ¬ (falsy ⊥) := by simp [Maybe.falsy]

def Maybe.defined : OrderHom Maybe Prop where
  toFun a := a ≠ ⊥
  monotone' a b h := by cases h <;> simp [*]

theorem Maybe.chain_defined (c : Chain Maybe) (n : ℕ) (h : (c n).defined)
  : ∀ k ≥ n, (c k).defined
  := sorry

open Classical in
noncomputable instance Maybe.instOmegaCompletePartialOrder : OmegaCompletePartialOrder Maybe where
  ωSup c := if h : ∃ n, (c n).defined then c h.choose else ⊥
  le_ωSup c i := sorry
  ωSup_le c a h := sorry

def Maybe.not : InfHom Maybe Maybe where
  toFun
  | 1 => 0
  | 0 => 1
  | ⊥ => ⊥
  map_inf' a b := by cases a <;> cases b <;> simp

@[simp] theorem Maybe.not_yes : Maybe.not 1 = 0 := rfl

@[simp] theorem Maybe.not_no : Maybe.not 0 = 1 := rfl

@[simp] theorem Maybe.not_maybe : Maybe.not ⊥ = ⊥ := rfl

@[simp] theorem Maybe.not_truthy_iff (m : Maybe) : m.not.truthy ↔ m.falsy := by cases m <;> simp

@[simp] theorem Maybe.not_falsy_iff (m : Maybe) : m.not.falsy ↔ m.truthy := by cases m <;> simp

instance Maybe.instMul : Mul Maybe where
  mul
    | 1, b => b
    | 0, _ => 0
    | ⊥, 0 => 0
    | ⊥, _ => ⊥

abbrev Maybe.and (a b : Maybe) : Maybe := a * b

instance Maybe.instMonoidWithZero : MonoidWithZero Maybe where
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_mul a := by cases a <;> rfl
  mul_zero a := by cases a <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl

@[simp] theorem Maybe.and_idem (a : Maybe) : a * a = a := by cases a <;> rfl

@[simp]
theorem Maybe.and_truthy_iff (a b : Maybe) :
  (a * b).truthy ↔ a.truthy ∧ b.truthy := by
  cases a <;> cases b <;> simp [*]

@[simp]
theorem Maybe.and_falsy_iff (a b : Maybe) :
  (a * b).falsy ↔ a.falsy ∨ b.falsy :=
  by cases a <;> cases b <;> simp [*]

instance Maybe.instAdd : Add Maybe where
  add
    | 1, _ => 1
    | 0, b => b
    | ⊥, 1 => 1
    | ⊥, _ => ⊥

@[simp] theorem Maybe.yes_or (b : Maybe) : 1 + b = 1 := by cases b <;> rfl

@[simp] theorem Maybe.or_yes (a : Maybe) : a + 1 = 1 := by cases a <;> rfl

@[simp] theorem Maybe.or_idem (a : Maybe) : a + a = a := by cases a <;> rfl

theorem Maybe.not_or (a b : Maybe) : not (a + b) = not a * not b := by
  cases a <;> cases b <;> rfl

theorem Maybe.not_and (a b : Maybe) : not (a * b) = not a + not b := by
  cases a <;> cases b <;> rfl

instance Maybe.instAddZeroClass : AddZeroClass Maybe where
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl

instance Maybe.instAddMonoid : AddMonoid Maybe where
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  nsmul | 0, _ => 0
        | _ + 1, a => a
  nsmul_succ n a := by cases n <;> simp

instance Maybe.instCommSemiring : CommSemiring Maybe where
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl

instance Maybe.instIsOrderedAddMonoid : IsOrderedAddMonoid Maybe where
  add_le_add_left a b h c := by cases h <;> cases c <;> simp [*]

instance Maybe.instIsOrderedMonoid : IsOrderedMonoid Maybe where
  mul_le_mul_left a b h c := by cases h <;> cases c <;> simp [*]

def Maybe.imp : Maybe → Maybe → Maybe
  | 1, b => b
  | 0, _ => 1
  | _, 1 => 1
  | ⊥, ⊥ => 1
  | ⊥, _ => ⊥

@[simp] theorem Maybe.imp_refl (a : Maybe) : imp a a = 1 := by cases a <;> rfl

@[simp] theorem Maybe.yes_imp (b : Maybe) : imp 1 b = b := rfl

@[simp] theorem Maybe.no_imp (b : Maybe) : imp 0 b = 1 := rfl

@[simp] theorem Maybe.imp_yes (a : Maybe) : imp a 1 = 1 := by cases a <;> rfl

@[simp] theorem Maybe.imp_no (a : Maybe) : imp a 0 = not a := by cases a <;> rfl

@[simp]
theorem Maybe.not_or_le_imp (a b : Maybe) : not a + b ≤ imp a b := by cases a <;> cases b <;> simp

@[simp] theorem Maybe.imp_truthy_truthy {a b : Maybe} : (imp a b).truthy → a.truthy → b.truthy := by
  cases a <;> cases b <;> simp [*]

@[simp] theorem Maybe.imp_truthy_falsy {a b : Maybe} : (imp a b).truthy → b.falsy → a.falsy := by
  cases a <;> cases b <;> simp [*]

@[simp] theorem Maybe.imp_falsy_truthy {a b : Maybe} : (imp a b).falsy → b.truthy → a.falsy := by
  cases a <;> cases b <;> simp [*]

@[simp] theorem Maybe.imp_falsy_not_truthy {a b : Maybe} : (imp a b).falsy → ¬b.truthy := by
  cases a <;> cases b <;> simp [*]

@[simp] theorem Maybe.imp_falsy_not_falsy {a b : Maybe} : (imp a b).falsy → ¬a.falsy := by
  cases a <;> cases b <;> simp [*]

theorem Maybe.imp_comm_iff (a b : Maybe) :
  imp a b = imp b a ↔ a = b := by
  cases a <;> cases b <;> simp [*]

def Maybe.eq : Maybe → Maybe → Maybe
  | 1, 1 => 1
  | 0, 0 => 1
  | ⊥, ⊥ => 1
  | ⊥, _ => ⊥
  | _, ⊥ => ⊥
  | _, _ => 0

@[simp] theorem Maybe.eq_refl (a : Maybe) : eq a a = 1 := by cases a <;> rfl

@[simp] theorem Maybe.maybe_eq_zero : eq ⊥ 0 = ⊥ := rfl

@[simp] theorem Maybe.maybe_eq_yes : eq ⊥ 1 = ⊥ := rfl

@[simp] theorem Maybe.zero_eq_maybe : eq 0 ⊥ = ⊥ := rfl

@[simp] theorem Maybe.yes_eq_maybe : eq 1 ⊥ = ⊥ := rfl

@[simp] theorem Maybe.yes_eq_no : eq 1 0 = 0 := rfl

@[simp] theorem Maybe.no_eq_yes : eq 0 1 = 0 := rfl

@[simp]
theorem Maybe.eq_truthy_iff {a b : Maybe} : (eq a b).truthy ↔ a = b := by
  cases a <;> cases b <;> simp [*]

theorem Maybe.eq_comm (a b : Maybe) : eq a b = eq b a := by
  cases a <;> cases b <;> simp

@[simp]
theorem Maybe.iff_and_iff (a b : Maybe) :
  (imp a b) * (imp b a) = eq a b := by
  cases a <;> cases b <;> simp

-/

inductive Symbol
  | ix : ℕ → Symbol

inductive Expr
  | sym : Symbol → Expr
  | getFv : Expr → Expr
  | getBv : ℕ → Expr → Expr
  | tt : Expr | ff : Expr | fail : Expr

/-

namespace Sem

structure Dict (α) where
  keys : Finset String
  vals : ∀ k ∈ keys, α

def Dict.repeat {α} (keys : Finset String) (val : α) : Dict α :=
  { keys := keys, vals := fun _ _ => val }

def Dict.ofVal {α} (val : α) : Dict α := .repeat {""} val

def Dict.getVal! {α} [Bot α] (d : Dict α) (k : String) : α :=
  if h : k ∈ d.keys then d.vals k h else ⊥

def Dict.map {α β} (f : α → β) (d : Dict α) : Dict β :=
  { keys := d.keys, vals := fun k h => f (d.vals k h) }

-- def Dict.toSome? {α} (d : Dict (Option α)) : Option (Dict α) :=
--   if h : ∀ k, (h : k ∈ d.keys) → (d.vals k h).isSome then
--     some { keys := d.keys, vals := fun k h => Option.get (d.vals k h) (h k h) }
--   else none

-- def Dict.tryMap? {α β} (f : α → Option β) (d : Dict α) : Option (Dict β)
--   := sorry

def Dict.restrict {α} (d : Dict α) (keys' : Finset String) : Dict α :=
  { keys := d.keys ∩ keys', vals := fun k h => d.vals k (Finset.mem_inter.mp h).1 }

instance {α : Type _} : Bot (Dict α) where
  bot := { keys := ∅, vals := fun k h => by simp at h }

instance {α : Type _} [Preorder α] : Preorder (Dict α) where
  le d1 d2 := d1.keys ⊆ d2.keys ∧ ∀ k h h', d1.vals k h ≤ d2.vals k h'
  le_refl d := by simp
  le_trans a b c hab hbc :=
    ⟨hab.1.trans hbc.1, fun k h h' => (hab.2 k h (hab.1 h)).trans (hbc.2 k (hab.1 h) h')⟩

instance {α : Type _} [PartialOrder α] : PartialOrder (Dict α) where
  le_antisymm a b hab hba := by
    cases a; cases b; cases hab.1.antisymm hba.1
    simp only [Dict.mk.injEq, heq_eq_eq, true_and]
    funext k h
    apply le_antisymm
    · apply hab.2
    · apply hba.2

inductive Expr
  | fv : String -> Expr
  | bv : String → Nat → Expr
  | erased : Expr → Expr
  | bool (φ : Prop) : Expr
  | app (f : Expr) (keys: Finset String) (vals : ∀ k ∈ keys, Expr) : Expr
  | abs (keys : Finset String) (body : Expr) : Expr
  | quote (e : Expr) : Expr
  | eval (e : Expr) : Expr
  -- | imp (e1 e2 : Expr) : Expr
  | dict (keys : Finset String) (vals : ∀ k ∈ keys, Expr) : Expr
  | symbols (keys : Finset String) : Expr
  | getKeys (e : Expr) : Expr

def Expr.depth : Expr → Nat
  | .fv _ => 0
  | .bv _ _ => 0
  | .erased e => e.depth + 1
  | .bool _ => 0
  | .app f keys vals => f.depth ⊔ (keys.sup (fun k => if h : k ∈ keys then (vals k h).depth else 0))
  | .abs _ body => Nat.succ body.depth
  | .quote e => e.depth + 1
  -- | .imp e1 e2 => (e1.depth ⊔ e2.depth) + 1
  | .eval e => e.depth + 1
  | .dict keys vals => keys.sup (fun k => if h : k ∈ keys then (vals k h).depth else 0)
  | .symbols _ => 0
  | .getKeys e => e.depth + 1

inductive Val
  | unspec : Val
  | bool (φ : Prop) : Val
  | fn (f : Dict Expr → Val) : Val
  | quote (e : Expr) : Val
  | dict (keys : Finset String) (vals : ∀ k ∈ keys, Val) : Val
  | symbols (keys : Finset String) : Val

instance : Inhabited Val where
  default := .unspec

instance : Bot Val where
  bot := .unspec

inductive Val.refines : Val → Val → Prop
  | unspec : ∀ v, Val.refines .unspec v
  | bool : ∀ {φ}, Val.refines (.bool φ) (.bool φ)
  | fn : ∀ {f1 f2},
      (∀ dict, Val.refines (f1 dict) (f2 dict)) →
      Val.refines (.fn f1) (.fn f2)
  | quote : ∀ {e}, Val.refines (.quote e) (.quote e)
  | dict : ∀ {keys vals1 vals2},
      (∀ k h, Val.refines (vals1 k h) (vals2 k h)) →
      Val.refines (.dict keys vals1) (.dict keys vals2)
  | symbols : ∀ {keys}, Val.refines (.symbols keys) (.symbols keys)

attribute [simp] Val.refines.unspec

instance : PartialOrder Val where
  le := Val.refines
  le_refl a := by induction a <;> constructor <;> simp [*]
  le_trans a b c ha hb := by
    induction ha generalizing c <;> cases hb <;> constructor <;> grind
  le_antisymm a b ha hb := by
    induction ha <;> cases hb <;> simp <;> grind

instance : OrderBot Val where
  bot_le a := Val.refines.unspec a

-- TODO: Values in fact form an ω-CPO

structure Store where
  base : String → Val
  nested : String → List Val

instance : EmptyCollection Store where
  emptyCollection := { base := fun _ => .unspec, nested := fun _ => [] }

@[simp]
theorem Store.nested_emp (x : String) : (∅ : Store).nested x = [] := rfl

def Store.getFv (σ : Store) (x : String) : Val := σ.base x

def Store.getBv (σ : Store) (x : String) (n : Nat) : Val := ((σ.nested x).drop n).headD ⊥

@[simp]
theorem Store.getFv_emp (x : String) : (∅ : Store).getFv x = ⊥ := rfl

@[simp]
theorem Store.getBv_emp (x : String) (n : Nat) : (∅ : Store).getBv x n = ⊥ := by simp [Store.getBv]

instance : Preorder Store where
  le σ1 σ2 := ∀ x, σ1.getFv x ≤ σ2.getFv x ∧ ∀ n, σ1.getBv x n ≤ σ2.getBv x n
  le_refl σ x := by simp [*]
  le_trans σ1 σ2 σ3 h12 h23 x := by grind

instance : OrderBot Store where
  bot := ∅
  bot_le σ x := by simp [*]

def Store.pushKey (σ : Store) (k : String) (v : Val) : Store where
  base := σ.base
  nested := fun x => if x = k then v :: σ.nested x else σ.nested x

-- TODO: pushKey mono

def Store.pushVal (σ : Store) (v : Val) : Store := σ.pushKey "" v

-- TODO: pushVal mono

theorem Store.pushKey_ne_comm (σ : Store) (a b : String) (va vb : Val) (h : a ≠ b) :
  (σ.pushKey a va).pushKey b vb = (σ.pushKey b vb).pushKey a va := by
  cases σ
  simp only [pushKey, mk.injEq, true_and]
  ext x
  split <;> split <;> simp only [*] at *

theorem Store.pushKey_eq_comm (σ : Store) (a b : String) (v : Val) :
  (σ.pushKey a v).pushKey b v = (σ.pushKey b v).pushKey a v := by
  cases σ
  simp only [pushKey, mk.injEq, true_and]
  ext x
  split <;> split <;> simp only [*] at *

theorem Store.pushKey_comm_of_eq_imp
  (σ : Store) (a b : String) (va vb : Val) (h : a = b → va = vb) :
  (σ.pushKey a va).pushKey b vb = (σ.pushKey b vb).pushKey a va := by
  by_cases he : a = b
  · cases (h he); exact Store.pushKey_eq_comm σ a b va
  · exact Store.pushKey_ne_comm σ a b va vb he

theorem Store.pushKey_comm_of_fn
  (σ : Store) (a b : String) (f : String → Val) :
  (σ.pushKey a (f a)).pushKey b (f b) = (σ.pushKey b (f b)).pushKey a (f a) :=
  Store.pushKey_comm_of_eq_imp σ a b (f a) (f b) (congrArg f)

def Store.pushFnKey (args : String → Val) (σ : Store) (key : String) : Store :=
  σ.pushKey key (args key)

-- TODO: pushFnKey mono

instance Store.pushFnKey_RightCommutative {args : String → Val}
  : RightCommutative (Store.pushFnKey args) where
  right_comm σ a b := σ.pushKey_comm_of_fn a b args

def Store.pushFnKeys (σ : Store) (keys : Finset String) (vals : String → Val) : Store :=
  keys.val.foldl (Store.pushFnKey vals) σ

-- TODO: pushFnKeys mono

def Store.pushDict (σ : Store) (dict : Dict Val) : Store :=
  σ.pushFnKeys dict.keys dict.getVal!

-- TODO: pushDict mono _in both arguments_

def Store.popKey (σ : Store) (key : String) : Store where
  base := σ.base
  nested := fun x => if x = key then (σ.nested x).tail else σ.nested x

-- TODO: popKey mono

instance Store.popKey_RightCommutative
  : RightCommutative Store.popKey where
  right_comm σ a b := by
    cases σ
    simp only [popKey, mk.injEq, true_and]
    ext x
    split <;> split <;> simp only [*] at *

def Store.popKeys (σ : Store) (keys : Finset String) : Store :=
  keys.val.foldl Store.popKey σ

-- TODO: popKeys mono

def Val.getKeys (v : Val) : Val := match v with
  | .dict keys _ => .symbols keys
  | _ => ⊥

-- Later:
  -- app quotes => quote app
  -- abs_quote => quote abs
    -- TODO: dynamic keys for abs_quote ==> Finset String support
    -- TODO: _general_ dynamic keys?

def Val.is_theorem (v : Val) : Prop := match v with
  | .bool φ => φ
  | .fn f => ∀ dict, Val.is_theorem (f dict) -- TODO: think about this...
  | _ => False

def Val.maybe_theorem (v : Val) : Prop := match v with
  | .bool φ => φ
  | .fn f => ∀ dict, Val.is_theorem (f dict) -- TODO: think about this...
  | ⊥ => True
  | _ => False

def Val.app (f : Val) (dict : Dict Expr) : Val := match f with
  | .bool b => .bool b
  | .fn f => f dict
  -- | .quote e => sorry
  | _ => ⊥

-- inductive Val.imp : Val → Val → Prop
--   | ff : ∀ v, imp (.bool False) v
--   | tt : ∀ v, imp v (.bool True)
--   | app {v1 v2} : (∀ dict, imp (v1.app dict) (v2.app dict)) → imp v1 v2

-- def Val.imp (v1 v2 : Val) : Val := match v1, v2 with
--   | .bool φ1, .bool φ2 => .bool (φ1 → φ2)
--   | .fn f1, .fn f2 => .bool (∀ dict, (Val.imp (f1 dict) (f2 dict)).is_theorem)
--   | _ , _ => ⊥

open Classical in
noncomputable def Store.eval? (σ : Store) (gas : ℕ) (e : Expr) : Val
  := match gas, e with
  | _, .fv x => σ.getFv x
  | _, .bv x n => σ.getBv x n
  | gas, .erased e => σ.eval? gas e
  | _, .bool φ => .bool φ
  | gas, .app f keys args => (σ.eval? gas f).app ⟨keys, args⟩
  | gas + 1, .abs keys body
    => .fn (fun dict => (σ.pushDict ((dict.restrict keys).map (σ.eval? gas))).eval? gas body)
  | _, .quote e => .quote e
  | gas + 1, .eval e => match σ.eval? gas e with
    | .quote e' => σ.eval? gas e'
    | _ => ⊥
  -- | gas, .imp e1 e2 => sorry
  | gas + 1, .dict keys vals =>
    .dict keys (fun k h => σ.eval? gas (vals k h))
  | _, .symbols keys => .symbols keys
  | gas, .getKeys e => (σ.eval? gas e).getKeys
  | 0, _ => ⊥

-- TODO: eval? is monotonic in the store

-- TODO: eval? is monotonic in gas

-- TODO: therefore, by ω-CPO, can define eval as the supremum of eval? over gas

-- TODO: show this satisfies the obvious equations:
  -- eval of fv/bv/unspec/bool are trivial
  -- eval of erased e is eval e
  -- eval of app f keys args is .app (eval f) ⟨keys, args⟩
  -- eval of abs keys body is .fn (fun dict => eval (pushDict (dict.restrict keys).map eval) body)
  -- eval (eval e) = eval e
  -- eval (quote e) = e

-- theorem Store.eval?_gas_le_succ (σ : Store) (e : Expr) (gas)
-- : σ.eval? gas e ≤ σ.eval? (gas + 1) e
--   := by induction e with
--   | app f _ _ hf =>
--     stop
--     simp only [eval?]
--     split
--     case h_1 h =>
--       rw [h] at hf
--       generalize hfg : σ.eval? (gas + 1) f = fg at *
--       cases hf
--       simp only
--     case h_2 => simp [*]
--   | abs => sorry
--   | _ =>
--     simp [eval?, *]

-- theorem Store.eval?_gas_mono (σ : Store) (e : Expr) {g1 g2} (h : g1 ≤ g2)
--   : σ.eval? g1 e ≤ σ.eval? g2 e := by
--   induction h with
--   | _ => sorry



end Sem

-/

end Gt3
