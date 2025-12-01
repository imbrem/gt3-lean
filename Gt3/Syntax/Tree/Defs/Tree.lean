import Gt3.Syntax.Tree.Children

namespace Gt3

open NumChildren BinderList HasChildren CastLE

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

@[match_pattern]
abbrev Tree.node {α} [NumChildren α]
  (tag : α) (children : Fin (numChildren tag) → Tree α) : Tree α :=
  ⟨tag, children⟩

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

-- instance Node.instCastLE {ι} [PartialOrder ι] {α}
--   [∀ n, BinderList (α n)] {β} [BindCastLE α] [CastLE β]
--   : BindCastLE (fun k : ι => Node (α k) (β k)) where
--   castLE h n := ⟨castLE h n.tag, fun i => castLE h (n.children (i.cast sorry))⟩
--   castLE_refl | ⟨_, _⟩ => by sorry
--   castLE_castLE h1 h2 | ⟨_, _⟩ => by sorry
--   castLE_hom h := sorry

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
