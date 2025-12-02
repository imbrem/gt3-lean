import Gt3.Tree.Tag

import Gt3.Universe.Level

namespace Gt3

open NumChildren BinderList

/-- The maximum size of a node in the GT3 core calculus : this is `natrec` -/
def maxCoreSize : ℕ := 4

/-- A node size for a node in the GT3 core calculus -/
def CoreSize : Type := Fin (maxCoreSize + 1)

instance CoreSize.ofN0 : OfNat CoreSize 0 := ⟨⟨0, by decide⟩⟩

instance CoreSize.ofN1 : OfNat CoreSize 1 := ⟨⟨1, by decide⟩⟩

instance CoreSize.ofN2 : OfNat CoreSize 2 := ⟨⟨2, by decide⟩⟩

instance CoreSize.ofN3 : OfNat CoreSize 3 := ⟨⟨3, by decide⟩⟩

instance CoreSize.ofN4 : OfNat CoreSize 4 := ⟨⟨4, by decide⟩⟩

instance CoreSize.instNumChildren : NumChildren CoreSize := instBinderListFin.toNumChildren

/-- The possible shapes for a node in the GT3 core calculus -/
inductive CoreShape : Type
  | constant : CoreShape
  | unary : CoreShape
  | binary : CoreShape
  | binder : CoreShape
  | ite : CoreShape
  | natrec : CoreShape

instance CoreShape.instNumChildren : NumChildren CoreShape where
  numChildren
    | .constant => 0
    | .unary => 1
    | .binary => 2
    | .binder => 2
    | .ite => 3
    | .natrec => 4

instance CoreShape.instBinderList : BinderList CoreShape where
  binderList
    | .constant => []
    | .unary => [0]
    | .binary => [0, 0]
    | .binder => [0, 1]
    | .ite => [0, 1, 1]
    | .natrec => [1, 1, 0, 0]

def CoreShape.size : CoreShape → CoreSize
  | .constant => 0
  | .unary => 1
  | .binary => 2
  | .binder => 2
  | .ite => 3
  | .natrec => 4

instance CoreShape.instNumChildrenHom : NumChildrenHom CoreShape.size where
  numChildren_hom h := by cases h <;> rfl

/-- A core-shaped tree -/
inductive CoreTree (α : List ℕ → Type _) : Type _ where
  | constant (h : α []) : CoreTree α
  | unary (h : α [0]) (arg : CoreTree α) : CoreTree α
  | binary (h : α [0, 0]) (left right : CoreTree α) : CoreTree α
  | binder (h : α [0, 1]) (body : CoreTree α) (ty : CoreTree α) : CoreTree α
  | ite (h : α [0, 1, 1]) (cond thenBr elseBr : CoreTree α) : CoreTree α
  | natrec (h : α [1, 1, 0, 0])
      (mot : CoreTree α)
      (succCase : CoreTree α)
      (zeroCase : CoreTree α)
      (scrut : CoreTree α)
      : CoreTree α

/-- A core-shaped de-Bruijn tree -/
inductive DCoreTree (α : List ℕ → Type) : ℕ → Type _ where
  | constant {k} (h : α [] ) : DCoreTree α k
  | unary {k} (h : α [0]) (arg : DCoreTree α k) : DCoreTree α k
  | binary {k} (h : α [0, 0]) (left right : DCoreTree α k) : DCoreTree α k
  | binder {k} (h : α [0, 1])
      (body : DCoreTree α (k + 1))
      (ty : DCoreTree α k)
      : DCoreTree α k
  | ite {k} (h : α [0, 1, 1])
      (cond : DCoreTree α k)
      (thenBr : DCoreTree α (k + 1))
      (elseBr : DCoreTree α (k + 1))
      : DCoreTree α k
  | natrec {k} (h : α [1, 1, 0, 0])
      (mot : DCoreTree α (k + 1))
      (succCase : DCoreTree α (k + 1))
      (zeroCase : DCoreTree α k)
      (scrut : DCoreTree α k)
      : DCoreTree α k

/-- A forded core-shaped tree -/
inductive FCoreTree (α : Type _) [BinderList α] : Type _ where
  | constant (h : α) (hh : binderList h = []) : FCoreTree α
  | unary (h : α) (hh : binderList h = [0]) (arg : FCoreTree α) : FCoreTree α
  | binary (h : α) (hh : binderList h = [0, 0]) (left right : FCoreTree α) : FCoreTree α
  | binder (h : α) (hh : binderList h = [0, 1])
      (body : FCoreTree α)
      (ty : FCoreTree α)
      : FCoreTree α
  | ite (h : α) (hh : binderList h = [0, 1, 1])
      (cond : FCoreTree α)
      (thenBr : FCoreTree α)
      (elseBr : FCoreTree α)
      : FCoreTree α
  | natrec (h : α) (hh : binderList h = [1, 1, 0, 0])
      (mot : FCoreTree α)
      (succCase : FCoreTree α)
      (zeroCase : FCoreTree α)
      (scrut : FCoreTree α)
      : FCoreTree α

/-- A fordered core-shaped de-Bruijn tree -/
inductive FDCoreTree (α : Type _) [BinderList α] : ℕ → Type _ where
  | constant {k} (h : α) (hh : binderList h = []) : FDCoreTree α k
  | unary {k} (h : α) (hh : binderList h = [0]) (arg : FDCoreTree α k) : FDCoreTree α k
  | binary {k} (h : α) (hh : binderList h = [0, 0]) (left right : FDCoreTree α k) : FDCoreTree α k
  | binder {k} (h : α) (hh : binderList h = [0, 1])
      (body : FDCoreTree α (k + 1))
      (ty : FDCoreTree α k)
      : FDCoreTree α k
  | ite {k} (h : α) (hh : binderList h = [0, 1, 1])
      (cond : FDCoreTree α k)
      (thenBr : FDCoreTree α (k + 1))
      (elseBr : FDCoreTree α (k + 1))
      : FDCoreTree α k
  | natrec {k} (h : α) (hh : binderList h = [1, 1, 0, 0])
      (mot : FDCoreTree α (k + 1))
      (succCase : FDCoreTree α (k + 1))
      (zeroCase : FDCoreTree α k)
      (scrut : FDCoreTree α k)
      : FDCoreTree α k

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

def BTm.coreShape {bs : List ℕ} : BTm bs → CoreShape
  | .univ _ => .constant
  | .empty => .constant
  | .unit => .constant
  | .null => .constant
  | .eqn => .binary
  | .pi => .binder
  | .sigma => .binder
  | .abs => .binder
  | .app => .binary
  | .pair => .binary
  | .fst => .unary
  | .snd => .unary
  | .dite => .ite
  | .trunc => .unary
  | .choose => .binder
  | .nats => .constant
  | .zero => .constant
  | .succ => .unary
  | .natrec => .natrec
  | .has_ty => .binary
  | .invalid => .constant

def STm.coreShape {k : ℕ} : STm k → CoreShape
  | .univ _ => .constant
  | .empty => .constant
  | .unit => .constant
  | .null => .constant
  | .eqn => .binary
  | .pi => .binder
  | .sigma => .binder
  | .abs => .binder
  | .app => .binary
  | .pair => .binary
  | .fst => .unary
  | .snd => .unary
  | .dite => .ite
  | .trunc => .unary
  | .choose => .binder
  | .nats => .constant
  | .zero => .constant
  | .succ => .unary
  | .natrec => .natrec
  | .has_ty => .binary
  | .invalid => .constant

def HTm.coreShape : HTm → CoreShape
  | .univ _ => .constant
  | .empty => .constant
  | .unit => .constant
  | .null => .constant
  | .eqn => .binary
  | .pi => .binder
  | .sigma => .binder
  | .abs => .binder
  | .app => .binary
  | .pair => .binary
  | .fst => .unary
  | .snd => .unary
  | .dite => .ite
  | .trunc => .unary
  | .choose => .binder
  | .nats => .constant
  | .zero => .constant
  | .succ => .unary
  | .natrec => .natrec
  | .has_ty => .binary
  | .invalid => .constant

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
