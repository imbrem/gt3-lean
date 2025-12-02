import Gt3.Syntax.Tree.Defs.Index
import Gt3.Syntax.Tree.Children

namespace Gt3

open NumChildren BinderList HasChildren CastLE

/-- A single node -/
structure Node (α : Type _) [NumChildren α] (β : Type _) : Type _ where
  tag : α
  children : Fin (numChildren tag) → β

instance Node.instNumChildren {α} [NumChildren α] {β} : NumChildren (Node α β) where
  numChildren n := numChildren n.tag

instance Node.instBinderList {α} [BinderList α] {β} : BinderList (Node α β) where
  binderList n := binderList n.tag

instance Node.instHasChildren {α} [BinderList α] {β} : HasChildren (Node α β) (fun _ => β) where
  getDChild n := n.children

instance Node.instFlatChildren {α} [BinderList α] {β} : FlatChildren (Node α β) β where

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

instance Node.instInhabited {α} [Inhabited α] [NumChildren α] {β} [Inhabited β]
  : Inhabited (Node α β) := ⟨⟨default, fun _ => default⟩⟩

end Gt3
