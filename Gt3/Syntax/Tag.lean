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

inductive CoreTag : Type
  | univ (ℓ : ULevel) : CoreTag
  | empty  : CoreTag
  | unit  : CoreTag
  | null  : CoreTag
  | eqn  : CoreTag
  | pi : CoreTag
  | sigma : CoreTag
  | abs : CoreTag
  | app : CoreTag
  | pair : CoreTag
  | fst : CoreTag
  | snd : CoreTag
  | dite : CoreTag
  | trunc : CoreTag
  | choose : CoreTag
  | nats : CoreTag
  | zero : CoreTag
  | succ : CoreTag
  | natrec : CoreTag
  | has_ty  : CoreTag
  | invalid  : CoreTag

inductive LCoreTag : ℕ → Type
  | univ (ℓ : ULevel) : LCoreTag 0
  | empty  : LCoreTag 0
  | unit  : LCoreTag 0
  | null  : LCoreTag 0
  | eqn  : LCoreTag 2
  | pi : LCoreTag 2
  | sigma : LCoreTag 2
  | abs : LCoreTag 2
  | app : LCoreTag 2
  | pair : LCoreTag 2
  | fst : LCoreTag 1
  | snd : LCoreTag 1
  | dite : LCoreTag 3
  | trunc : LCoreTag 1
  | choose : LCoreTag 2
  | nats : LCoreTag 0
  | zero : LCoreTag 0
  | succ : LCoreTag 1
  | natrec : LCoreTag 4
  | has_ty  : LCoreTag 2
  | invalid  : LCoreTag 0

inductive DCoreTag : List ℕ → Type
  | univ (ℓ : ULevel) : DCoreTag []
  | empty  : DCoreTag []
  | unit  : DCoreTag []
  | null  : DCoreTag  []
  | eqn  : DCoreTag [0, 0]
  | pi : DCoreTag [0, 1]
  | sigma : DCoreTag [0, 1]
  | abs : DCoreTag [0, 1]
  | app : DCoreTag [0, 0]
  | pair : DCoreTag [0, 0]
  | fst : DCoreTag [0]
  | snd : DCoreTag [0]
  | dite : DCoreTag [0, 1, 1]
  | trunc : DCoreTag [0]
  | choose : DCoreTag [0, 1]
  | nats : DCoreTag []
  | zero : DCoreTag []
  | succ : DCoreTag [0]
  | natrec : DCoreTag [1, 1, 0, 0]
  | has_ty  : DCoreTag [0, 0]
  | invalid  : DCoreTag []

def DCoreTag.coreShape {bs : List ℕ} : DCoreTag bs → CoreShape
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

def LCoreTag.coreShape {k : ℕ} : LCoreTag k → CoreShape
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

def CoreTag.coreShape : CoreTag → CoreShape
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

def LCoreTag.toCoreTag {k : ℕ} : LCoreTag k → CoreTag
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

def DCoreTag.toLCoreTag {bs : List ℕ} : DCoreTag bs → LCoreTag (bs.length)
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

def DCoreTag.toCoreTag {bs : List ℕ} (x : DCoreTag bs) : CoreTag
  := x.toLCoreTag.toCoreTag

instance CoreTag.instNumChildren : NumChildren CoreTag where
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

instance LCoreTag.instNumChildren {k : ℕ} : NumChildren (LCoreTag k) where
  numChildren _ := k

instance DCoreTag.instNumChildren {bs : List ℕ} : NumChildren (DCoreTag bs) where
  numChildren _ := bs.length

instance CoreTag.instBinderList : BinderList CoreTag where
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

instance LCoreTag.instBinderList {k : ℕ} : BinderList (LCoreTag k) where
  binderList x := binderList x.toCoreTag

instance DCoreTag.instBinderList {bs : List ℕ} : BinderList (DCoreTag bs) where
  binderList _ := bs

instance CoreTag.instNumChildrenHomCoreShape : NumChildrenHom CoreTag.coreShape where
  numChildren_hom h := by cases h <;> rfl

instance LCoreTag.instNumChildrenHomCoreShape {k : ℕ}
  : NumChildrenHom (LCoreTag.coreShape (k := k)) where
  numChildren_hom h := by cases h <;> rfl

instance DCoreTag.instNumChildrenHomCoreShape {bs : List ℕ}
  : NumChildrenHom (DCoreTag.coreShape (bs := bs)) where
  numChildren_hom h := by cases h <;> rfl

instance LCoreTag.instBinderListHomToCoreTag {k : ℕ}
  : BinderListHom (LCoreTag.toCoreTag (k := k))
  := BinderListHom.mk' fun x => by cases x <;> rfl

instance DCoreTag.instBinderListHomToLCoreTag {bs : List ℕ}
  : BinderListHom (DCoreTag.toLCoreTag (bs := bs))
  := BinderListHom.mk' fun x => by cases x <;> rfl

instance DCoreTag.instBinderListHomToCoreTag {bs : List ℕ}
  : BinderListHom (DCoreTag.toCoreTag (bs := bs))
  := BinderListHom.mk' fun x => by cases x <;> rfl

end Gt3
