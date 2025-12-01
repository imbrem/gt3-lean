import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn

namespace Gt3

class NumChildren (α : Type _) where
  numChildren : α → ℕ

open NumChildren

class BinderList (α : Type _) extends NumChildren α where
  binderList : α → List ℕ
  binderTuple : (t : α) → Fin (numChildren t) → ℕ := fun t i => (binderList t)[i]!
  binderList_length : ∀ t, (binderList t).length = numChildren t
    := by intro t; (try cases t) <;> (try simp [binderList]) <;> rfl
  binderTuple_valid : ∀ (t : α) (i : Fin (numChildren t)), binderTuple t i = (binderList t)[i]!
    := by intro t i; (try cases t) <;> (try simp) <;> (try simp [binderTuple]) <;> rfl

-- protected abbrev BinderList.ofTuple {α} [NumChildren α]
--   (binderTuple : (t : α) → Fin (numChildren t) → ℕ) : BinderList α where
--   binderList t := List.ofFn (binderTuple t)
--   binderTuple := binderTuple

attribute [simp] BinderList.binderList_length

def BinderList.getBinder {α} [BinderList α] (t : α) (i : ℕ) : ℕ := (binderList t)[i]!

open BinderList

class ToHead (α β : Type _) where
  toHead : α → β

open ToHead

class TreeHom (α β : Type _) [NumChildren α] [NumChildren β] extends ToHead α β where
  numChildren_toHead : ∀ t, numChildren t = numChildren (toHead t) := by intro x; cases x <;> rfl

class BinderHom (α β : Type _) [BinderList α] [BinderList β] extends TreeHom α β where
  binderList_toHead : ∀ t, binderList t = binderList (toHead t) := by intro x; cases x <;> rfl

inductive WithVar (ι : Type _) (α : Type _) [NumChildren α] : Type _
  | fv (x : ι) : WithVar ι α
  | node (h : α) : WithVar ι α

instance WithVar.instNumChildren {ι α} [NumChildren α] : NumChildren (WithVar ι α) where
  numChildren
    | .fv _ => 0
    | .node h => numChildren h

instance WithVar.instBinderList {ι α} [BinderList α] : BinderList (WithVar ι α) where
  binderList
    | .fv _ => []
    | .node h => binderList h

inductive TreeN (α : Type _) : Type _
  | node (n : ℕ) (h : α) (children : Fin n → TreeN α) : TreeN α

instance TreeN.instNumChildren {α} : NumChildren (TreeN α) where
  numChildren
    | .node n _ _ => n

inductive ODTreeN (α : Type _) : Type _
  | bv (i : ℕ) : ODTreeN α
  | node (binders : List ℕ) (h : α) (children : Fin binders.length → ODTreeN α) : ODTreeN α

instance ODTreeN.instNumChildren {α} : NumChildren (ODTreeN α) where
  numChildren
    | .bv _ => 0
    | .node binders _ _ => binders.length

instance ODTreeN.instBinderList {α} : BinderList (ODTreeN α) where
  binderList
    | .bv _ => []
    | .node binders _ _ => binders

inductive DTreeN (α : Type _) : ℕ → Type _
  | bv {k} (i : Fin k) : DTreeN α k
  | node {k}
    (binders : List ℕ) (h : α)
    (children : (i : Fin binders.length) → DTreeN α (k + binders[i])) :
    DTreeN α k

instance DTreeN.instNumChildren {α} {k} : NumChildren (DTreeN α k) where
  numChildren
    | .bv _ => 0
    | .node binders _ _ => binders.length

instance DTreeN.instBinderList {α} {k} : BinderList (DTreeN α k) where
  binderList
    | .bv _ => []
    | .node binders _ _ => binders

inductive TreeN.ValidChildren {α} [NumChildren α] : TreeN α → Type _
  | node {n h children}
    (hh : n = numChildren h) (hchildren : ∀ i, TreeN.ValidChildren (children i)) :
    TreeN.ValidChildren (TreeN.node n h children)

inductive ODTreeN.ValidChildren {α} [BinderList α] : ODTreeN α → Type _
  | bv (i) : ODTreeN.ValidChildren (ODTreeN.bv i)
  | node {binders h children}
    (hh : binders = binderList h)
    (hchildren : ∀ i, ODTreeN.ValidChildren (children i)) :
    ODTreeN.ValidChildren (ODTreeN.node binders h children)

inductive DTreeN.ValidChildren {α : Type _} [BinderList α] : ∀ {k}, DTreeN α k → Type _
  | bv {k} (i : Fin k) : DTreeN.ValidChildren (DTreeN.bv i)
  | node {binders h children}
    (hh : binders = binderList h)
    (hchildren : ∀ i, DTreeN.ValidChildren (children i)) :
    DTreeN.ValidChildren (DTreeN.node binders h children)

--TODO: validator for treeN, odtreeN, dtreeN...

--TODO: erasure squares and friends...

--TODO: valid treeN => tree; valid odtreeN => odtree; valid dtreeN => dtree...

--TODO: substitution lore...

--TODO: opening lore...

--TODO: and so on...

inductive Tree (α : Type _) [NumChildren α] : Type _
  | node (t : α) (children : Fin (numChildren t) → Tree α) : Tree α

instance Tree.instNumChildren {α} [NumChildren α] : NumChildren (Tree α) where
  numChildren
    | .node h _ => numChildren h

instance Tree.instBinderList {α} [BinderList α] : BinderList (Tree α) where
  binderList
    | .node h _ => binderList h

inductive DTree (α : Type _) [BinderList α] : ℕ → Type _
  | bv {k} (i : Fin k) : DTree α k
  | node {k}
    (h : α) (children : (i : Fin (numChildren h)) → DTree α (k + getBinder h i)) : DTree α k

instance DTree.instNumChildren {α} [BinderList α] {k} : NumChildren (DTree α k) where
  numChildren
    | .bv _ => 0
    | .node h _ => numChildren h

instance DTree.instBinderList {α} [BinderList α] {k} : BinderList (DTree α k) where
  binderList
    | .bv _ => []
    | .node h _ => binderList h

inductive ODTree (α : Type _) [NumChildren α] : Type _
  | bv (i : ℕ) : ODTree α
  | node (h : α) (children : Fin (numChildren h) → ODTree α) : ODTree α

instance ODTree.instNumChildren {α} [NumChildren α] : NumChildren (ODTree α) where
  numChildren
    | .bv _ => 0
    | .node h _ => numChildren h

instance ODTree.instBinderList {α} [BinderList α] : BinderList (ODTree α) where
  binderList
    | .bv _ => []
    | .node h _ => binderList h

def DTree.eraseB {α} [BinderList α] {k} : DTree α k → ODTree α
  | .bv i => .bv (i.val)
  | .node h children => .node h (fun i => eraseB (children i))

inductive VTreeN (ι : Type _) (α : Type _) : Type _
  | fv (x : ι) : VTreeN ι α
  | node (n : ℕ) (h : α) (children : Fin n → VTreeN ι α) : VTreeN ι α

instance VTreeN.instNumChildren {ι α} : NumChildren (VTreeN ι α) where
  numChildren
    | .fv _ => 0
    | .node n _ _ => n

inductive VTreeN.validChildren {ι α} [NumChildren α] : VTreeN ι α → Prop
  | node {n h children}
    (hh : n = numChildren h) (hchildren : ∀ i, VTreeN.validChildren (children i)) :
    VTreeN.validChildren (VTreeN.node n h children)

inductive VTree' (ι : Type _) (α : Type _) [NumChildren α] : Type _
  | fv (x : ι) : VTree' ι α
  | node (h : α) (children : Fin (numChildren h) → VTree' ι α) : VTree' ι α

instance VTree'.instNumChildren {ι α} [NumChildren α] : NumChildren (VTree' ι α) where
  numChildren
    | .fv _ => 0
    | .node h _ => numChildren h

instance VTree'.instBinderList {ι α} [BinderList α] : BinderList (VTree' ι α) where
  binderList
    | .fv _ => []
    | .node h _ => binderList h

inductive DVTree' (ι : Type _) (α : Type _) [BinderList α] : ℕ → Type _
  | fv (x : ι) {k} : DVTree' ι α k
  | bv {k} (i : Fin k) : DVTree' ι α k
  | node {k}
    (t : α) (children : (i : Fin (numChildren t)) → DVTree' ι α (k + getBinder t i)) : DVTree' ι α k

instance DVTree'.instNumChildren {ι α} [BinderList α] {k} : NumChildren (DVTree' ι α k) where
  numChildren
    | .fv _ => 0
    | .bv _ => 0
    | .node h _ => numChildren h

instance DVTree'.instBinderList {ι α} [BinderList α] {k} : BinderList (DVTree' ι α k) where
  binderList
    | .fv _ => []
    | .bv _ => []
    | .node h _ => binderList h

inductive ODVTree' (ι : Type _) (α : Type _) [NumChildren α] : Type _
  | fv (x : ι) : ODVTree' ι α
  | bv (i : ℕ) : ODVTree' ι α
  | node (t : α) (children : ℕ → ODVTree' ι α) : ODVTree' ι α

instance ODVTree'.instNumChildren {ι α} [NumChildren α] : NumChildren (ODVTree' ι α) where
  numChildren
    | .fv _ => 0
    | .bv _ => 0
    | .node h _ => numChildren h

instance ODVTree'.instBinderList {ι α} [BinderList α] : BinderList (ODVTree' ι α) where
  binderList
    | .fv _ => []
    | .bv _ => []
    | .node h _ => binderList h

def maxNodeSize : ℕ := 4

def NodeSize : Type := Fin (maxNodeSize + 1)

inductive NodeShape : Type
  | constant : NodeShape
  | unary : NodeShape
  | binary : NodeShape
  | binder : NodeShape
  | ite : NodeShape
  | natrec : NodeShape

instance NodeShape.instNumChildren : NumChildren NodeShape where
  numChildren
    | .constant => 0
    | .unary => 1
    | .binary => 2
    | .binder => 2
    | .ite => 3
    | .natrec => 4

instance NodeShape.instBinderList : BinderList NodeShape where
  binderList
    | .constant => []
    | .unary => [0]
    | .binary => [0, 0]
    | .binder => [0, 1]
    | .ite => [0, 1, 1]
    | .natrec => [1, 1, 0, 0]

inductive FTree (α : ℕ → Type _) : Type _
  | node (n : ℕ) (h : α n) (children : Fin n → FTree α) : FTree α

inductive FVTree (ι : Type _) (α : ℕ → Type _) : Type _
  | fv (x : ι) : FVTree ι α
  | node (n : ℕ) (h : α n) (children : Fin n → FVTree ι α) : FVTree ι α

inductive STree (α : ℕ → Type _) : Type _
  | n0 (h : α 0) : STree α
  | n1 (h : α 1) (child : STree α) : STree α
  | n2 (h : α 2) (left right : STree α) : STree α
  | n3 (h : α 3) (c l r : STree α) : STree α
  | n4 (h : α 4) (c l r s : STree α) : STree α

--TODO: ShapeTrees

--TODO: ShapeTreesWithVars

end Gt3
