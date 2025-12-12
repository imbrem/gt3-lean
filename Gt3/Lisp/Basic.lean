import Mathlib.Data.Erased
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Lattice.Fold

namespace Gt3

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
  | unspec : Expr
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
  | .unspec => 0
  | .bool _ => 0
  | .app f keys vals => f.depth ⊔ (keys.sup (fun k => if h : k ∈ keys then (vals k h).depth else 0))
  | .abs _ body => Nat.succ body.depth
  | .quote e => e.depth + 1
  -- | .imp e1 e2 => (e1.depth ⊔ e2.depth) + 1
  | .eval e => e.depth + 1
  | .dict keys vals => keys.sup (fun k => if h : k ∈ keys then (vals k h).depth else 0)
  | .symbols _ => 0
  | .getKeys e => e.depth + 1

instance : Inhabited Expr where
  default := .unspec

instance : Bot Expr where
  bot := .unspec

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
  | _, .unspec => ⊥
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

end Gt3
