import Gt3.Syntax.General.Tag

namespace Gt3

open NumChildren BinderList

/-- A node equipped with a set of children of indexed type `β` -/
class HasChildren (α : Type _) [BinderList α] (β : ℕ → Type _) where
  getChild (t : α) : (i : Fin (numChildren t)) → (β (getBinder t i))

open HasChildren

class FlatChildren (α : Type _) [BinderList α] (β : Type _) extends HasChildren α (fun _ => β) where
  listChildren (t : α) : List β := List.ofFn (getChild t)
  listChildren_eq (t : α) : listChildren t = List.ofFn (getChild t) := by simp

/-- A single node -/
structure Node (α : Type _) [NumChildren α] (β : Type _) : Type _ where
  tag : α
  children : Fin (numChildren tag) → β

instance {α} [NumChildren α] {β} : NumChildren (Node α β) where
  numChildren n := numChildren n.tag

instance {α} [BinderList α] {β} : BinderList (Node α β) where
  binderList n := binderList n.tag

instance {α} [BinderList α] {β} : FlatChildren (Node α β) β where
  getChild n := n.children

/-- A tree of nodes -/
structure Tree (α : Type _) [NumChildren α] : Type _ where
  tag : α
  children : Fin (numChildren tag) → Tree α

instance {α} [NumChildren α] : NumChildren (Tree α) where
  numChildren t := numChildren t.tag

instance {α} [BinderList α] : BinderList (Tree α) where
  binderList t := binderList t.tag

instance {α} [BinderList α] : FlatChildren (Tree α) (Tree α) where
  getChild t := t.children

def Node.toTree {α} [NumChildren α] (n : Node α (Tree α)) : Tree α :=
  ⟨n.tag, n.children⟩

def Tree.toNode {α} [NumChildren α] (t : Tree α) : Node α (Tree α) :=
  ⟨t.tag, t.children⟩

instance Node.toTree_numChildrenHom {α} [NumChildren α] :
  NumChildrenHom (Node.toTree (α := α)) where
  numChildren_hom _ := rfl

instance Tree.toNode_numChildrenHom {α} [NumChildren α] :
  NumChildrenHom (Tree.toNode (α := α)) where
  numChildren_hom _ := rfl

instance Node.toTree_binderListHom {α} [BinderList α] :
  BinderListHom (Node.toTree (α := α)) where
  binderList_hom _ := rfl

instance Tree.toNode_binderListHom {α} [BinderList α] :
  BinderListHom (Tree.toNode (α := α)) where
  binderList_hom _ := rfl

@[simp]
theorem Tree.toNode_toTree {α} [NumChildren α] (t : Tree α) : t.toNode.toTree = t
  := by cases t; rfl

@[simp]
theorem Node.toTree_toNode {α} [NumChildren α] (n : Node α (Tree α)) : n.toTree.toNode = n
  := by cases n; rfl


/-- A single de-Bruijn node -/
inductive DNode (α : ℕ → Type _) [∀ k, BinderList (α k)] (β : ℕ → Type _) (k : ℕ) : Type _
  | bv (i : Fin k) : DNode α β k
  | node (h : α k) (children : (i : Fin (numChildren h)) → (β (getBinder h i))) : DNode α β k

instance {α} [∀ k, BinderList (α k)] {β} {k} : BinderList (DNode α β k) where
  numChildren
    | .bv _ => 0
    | .node h _ => numChildren h
  binderList
    | .bv _ => []
    | .node h _ => binderList h
  getBinder
    | .bv _ => unreachable!
    | .node h _ => getBinder h
  getBinder_eq h i := by cases h <;> simp only [getBinder_eq]; rfl

instance {α} [∀ k, BinderList (α k)] {β} {k} : HasChildren (DNode α β k) β where
  getChild
    | .bv _ => fun i => i.elim0
    | .node _ children => children

/-- A tree of de-Bruijn nodes -/
inductive DTree (α : ℕ → Type _) [∀ k, BinderList (α k)] : ℕ → Type _
  | bv {k} (i : Fin k) : DTree α k
  | node {k}
    (h : α k) (children : (i : Fin (numChildren h)) → DTree α (k + getBinder h i)) : DTree α k

instance {α} [∀ k, BinderList (α k)] {k} : BinderList (DTree α k) where
  numChildren
    | .bv _ => 0
    | .node h _ => numChildren h
  binderList
    | .bv _ => []
    | .node h _ => binderList h
  getBinder
    | .bv _ => unreachable!
    | .node h _ => getBinder h
  getBinder_eq h i := by cases h <;> simp only [getBinder_eq]; rfl

instance {α} [∀ k, BinderList (α k)] {k} : HasChildren (DTree α k) (fun b => DTree α (k + b))
  where getChild
  | .bv _ => fun i => i.elim0
  | .node _ children => children

/-- A variable or a value -/
inductive Var (ι : Type _) (α : Type _) : Type _
  | fv (x : ι) : Var ι α
  | val (h : α) : Var ι α

instance {ι α} [NumChildren α] : NumChildren (Var ι α) where
  numChildren
    | .fv _ => 0
    | .val h => numChildren h

instance {ι α} [BinderList α] : BinderList (Var ι α) where
  binderList
    | .fv _ => []
    | .val h => binderList h
  getBinder
    | .fv _ => unreachable!
    | .val h => getBinder h
  getBinder_eq h i := by cases h <;> simp only [getBinder_eq] <;> rfl

instance {ι α β} [BinderList α] [HasChildren α β]
  : HasChildren (Var ι α) β where
  getChild
    | .fv _ => fun i => i.elim0
    | .val h => getChild h

def Node.map {α α' β β'} [NumChildren α] [NumChildren α']
  (f : α → α') [hf : NumChildrenHom f]
  (g : β → β') (n : Node α β) : Node α' β' :=
  ⟨f n.tag, fun i => g (n.children (i.cast (hf.numChildren_hom n.tag)))⟩

def Node.mapTag {α α' β} [NumChildren α] [NumChildren α']
  (f : α → α') [hf : NumChildrenHom f] (n : Node α β) : Node α' β := n.map f id

def Node.mapChildren {α β β'} [NumChildren α] (f : β → β') (n : Node α β) : Node α β' :=
  ⟨n.tag, fun i => f (n.children i)⟩

instance Node.instFunctor {α} [NumChildren α] : Functor (Node α) where
  map := Node.mapChildren

instance Node.instLawfulFunctor {α} [NumChildren α] : LawfulFunctor (Node α) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

def Node.mapToTree {α α' β} [NumChildren α] [NumChildren α']
  (f : α → α') [hf : NumChildrenHom f]
  (g : β → Tree α')
  (n : Node α β) : Node α' (Tree α') :=
  ⟨f n.tag, fun i => g (n.children (i.cast (hf.numChildren_hom n.tag)))⟩

def Node.treeChildren {α β} [NumChildren α] (n : Node α β) (f : β → Tree α) : Tree α :=
  ⟨n.tag, fun i => f (n.children i)⟩

instance Node.map_numChildrenHom {α α' β β'} [NumChildren α] [NumChildren α']
  (f : α → α') [hf : NumChildrenHom f] (g : β → β')
  : NumChildrenHom (Node.map f g) where
  numChildren_hom _ := hf.numChildren_hom _

instance Node.mapTag_numChildrenHom {α α' β} [NumChildren α] [NumChildren α']
  (f : α → α') [hf : NumChildrenHom f]
  : NumChildrenHom (Node.mapTag (β := β) f) where
  numChildren_hom _ := hf.numChildren_hom _

instance Node.mapChildren_numChildrenHom {α β β'} [NumChildren α]
  (f : β → β') : NumChildrenHom (Functor.map (f := Node α) f) where
  numChildren_hom _ := rfl

instance Node.mapToTree_numChildrenHom {α α' β} [NumChildren α] [NumChildren α']
  (f : α → α') [hf : NumChildrenHom f] (g : β → Tree α') : NumChildrenHom (Node.mapToTree f g) where
  numChildren_hom _ := hf.numChildren_hom _

def Tree.map {α α'} [NumChildren α] [NumChildren α']
  (f : α → α') [hf : NumChildrenHom f] : Tree α → Tree α'
  | .mk tag children => ⟨f tag, fun i => (children (i.cast (hf.numChildren_hom tag))).map f⟩

instance Tree.map_numChildrenHom {α α'} [NumChildren α] [NumChildren α']
  (f : α → α') [hf : NumChildrenHom f] : NumChildrenHom (Tree.map f) where
  numChildren_hom t := by cases t ; simp [numChildren, map, hf.numChildren_hom]

instance Tree.map_binderListHom {α α'} [BinderList α] [BinderList α']
  (f : α → α') [hf : BinderListHom f] : BinderListHom (Tree.map f) where
  binderList_hom t := by cases t ; simp [binderList, map, hf.binderList_hom]


end Gt3
