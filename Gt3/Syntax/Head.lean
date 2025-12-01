import Mathlib.Data.List.Basic

import Gt3.Universe.Level

namespace Gt3

class NumChildren (α : Type _) where
  numChildren : α → ℕ

open NumChildren

class BinderList (α : Type _) extends NumChildren α where
  binderList : α → List ℕ
  binderList_length : ∀ t, (binderList t).length = numChildren t := by intro x; cases x <;> rfl

open BinderList

inductive HTm : Type
  | univ (ℓ : ULevel) : HTm
  | empty  : HTm
  | unit  : HTm
  | null  : HTm
  | eqn  : HTm
  | pi : HTm
  | sigma : HTm
  | abs : HTm
  | app : HTm
  | pair : HTm
  | fst : HTm
  | snd : HTm
  | dite : HTm
  | trunc : HTm
  | choose : HTm
  | nats : HTm
  | zero : HTm
  | succ : HTm
  | natrec : HTm
  | has_ty  : HTm
  | invalid  : HTm

inductive BTm : List ℕ → Type
  | univ (ℓ : ULevel) : BTm []
  | empty  : BTm []
  | unit  : BTm []
  | null  : BTm  []
  | eqn  : BTm [0, 0]
  | pi : BTm [0, 1]
  | sigma : BTm [0, 1]
  | abs : BTm [0, 1]
  | app : BTm [0, 0]
  | pair : BTm [0, 0]
  | fst : BTm [0]
  | snd : BTm [0]
  | dite : BTm [0, 1, 1]
  | trunc : BTm [0]
  | choose : BTm [0, 1]
  | nats : BTm []
  | zero : BTm []
  | succ : BTm [0]
  | natrec : BTm [1, 1, 0, 0]
  | has_ty  : BTm [0, 0]
  | invalid  : BTm []

inductive STm : ℕ → Type
  | univ (ℓ : ULevel) : STm 0
  | empty  : STm 0
  | unit  : STm 0
  | null  : STm 0
  | eqn  : STm 2
  | pi : STm 2
  | sigma : STm 2
  | abs : STm 2
  | app : STm 2
  | pair : STm 2
  | fst : STm 1
  | snd : STm 1
  | dite : STm 3
  | trunc : STm 1
  | choose : STm 2
  | nats : STm 0
  | zero : STm 0
  | succ : STm 1
  | natrec : STm 4
  | has_ty  : STm 2
  | invalid  : STm 0

def BTm.toHTm {bs : List ℕ} : BTm bs → HTm
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn => .eqn
  | .pi => .pi
  | .sigma => .sigma
  | .abs => .abs
  | .app => .app
  | .pair => .pair
  | .fst => .fst
  | .snd => .snd
  | .dite => .dite
  | .trunc => .trunc
  | .choose => .choose
  | .nats => .nats
  | .zero => .zero
  | .succ => .succ
  | .natrec => .natrec
  | .has_ty => .has_ty
  | .invalid => .invalid

def BTm.toSTm {bs : List ℕ} : BTm bs → STm (bs.length)
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn => .eqn
  | .pi => .pi
  | .sigma => .sigma
  | .abs => .abs
  | .app => .app
  | .pair => .pair
  | .fst => .fst
  | .snd => .snd
  | .dite => .dite
  | .trunc => .trunc
  | .choose => .choose
  | .nats => .nats
  | .zero => .zero
  | .succ => .succ
  | .natrec => .natrec
  | .has_ty => .has_ty
  | .invalid => .invalid

def STm.toHTm {k : ℕ} : STm k → HTm
  | .univ ℓ => .univ ℓ
  | .empty => .empty
  | .unit => .unit
  | .null => .null
  | .eqn => .eqn
  | .pi => .pi
  | .sigma => .sigma
  | .abs => .abs
  | .app => .app
  | .pair => .pair
  | .fst => .fst
  | .snd => .snd
  | .dite => .dite
  | .trunc => .trunc
  | .choose => .choose
  | .nats => .nats
  | .zero => .zero
  | .succ => .succ
  | .natrec => .natrec
  | .has_ty => .has_ty
  | .invalid => .invalid

@[simp]
theorem BTm.toSTm_toHTm {bs : List ℕ} (b : BTm bs) : b.toSTm.toHTm = b.toHTm := by cases b <;> rfl

instance HTm.instNumChildren : NumChildren HTm where
  numChildren
    | .univ _ => 0
    | .empty => 0
    | .unit => 0
    | .null => 0
    | .eqn => 2
    | .pi => 2
    | .sigma => 2
    | .abs => 2
    | .app => 2
    | .pair => 2
    | .fst => 1
    | .snd => 1
    | .dite => 3
    | .trunc => 1
    | .choose => 2
    | .nats => 0
    | .zero => 0
    | .succ => 1
    | .natrec => 4
    | .has_ty => 2
    | .invalid => 0

instance STm.numChildren {n} : NumChildren (STm n) where
  numChildren _ := n

instance BTm.numChildren {bs : List ℕ} : NumChildren (BTm bs) where
  numChildren _ := bs.length

instance HTm.instBinderList : BinderList HTm where
  binderList
    | .univ _ => []
    | .empty => []
    | .unit => []
    | .null => []
    | .eqn => [0, 0]
    | .pi => [0, 1]
    | .sigma => [0, 1]
    | .abs => [0, 1]
    | .app => [0, 0]
    | .pair => [0, 0]
    | .fst => [0]
    | .snd => [0]
    | .dite => [0, 1, 1]
    | .trunc => [0]
    | .choose => [0, 1]
    | .nats => []
    | .zero => []
    | .succ => [0]
    | .natrec => [1, 1, 0, 0]
    | .has_ty => [0, 0]
    | .invalid => []

instance STm.instBinderList {n} : BinderList (STm n) where
  binderList x := binderList x.toHTm

instance BTm.instBinderList {bs : List ℕ} : BinderList (BTm bs) where
  binderList x := bs

end Gt3
