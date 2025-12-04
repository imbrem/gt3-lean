import Gt3.Tree.Node

namespace Gt3

open NumChildren BinderList HasChildren FlatChildren

structure Graph (ι : Type _) (α : Type _) [NumChildren α] where
  getNode : ι → Node α ι

variable {ι ι₁ ι₂ α α'} [BinderList α] [BinderList α']

def Graph.getEdge (g : Graph ι α) (i : ι) (j : Fin (numChildren (g.getNode i))) : ι :=
  getChild (g.getNode i) j

def Graph.mapTags
  (f : α → α') [NumChildrenHom f] (g : Graph ι α) : Graph ι α' where
  getNode i := (g.getNode i).mapTag f

def Graph.mapIx
  (f : ι₁ → ι₂)
  (g : ι₂ → ι₁)
  (gr : Graph ι₁ α) : Graph ι₂ α where
  getNode i := (gr.getNode (g i)).mapChildren f

inductive Graph.IsPathFrom (g : Graph ι α) : ι → List ι → Prop
  | nil (i : ι) : Graph.IsPathFrom g i []
  | cons
    {head child : ι} (j) (hhead : getEdge g head j = child)
    {tail : List ι} (htail : Graph.IsPathFrom g child tail)
    : Graph.IsPathFrom g head (child :: tail)

inductive Graph.IsPathBetween (g : Graph ι α) : ι → ι → List ι → Prop
  | refl (i : ι) : Graph.IsPathBetween g i i []
  | cons
    {head child dest : ι} (j) (hhead : getEdge g head j = child)
    {tail : List ι} (htail : Graph.IsPathBetween g child dest tail)
    : Graph.IsPathBetween g head dest (child :: tail)

def Graph.pathsBetween (g : Graph ι α) (i₁ i₂ : ι) : Set (List ι)
  := { p | g.IsPathBetween i₁ i₂ p }

def Graph.AreConnected (g : Graph ι α) (i₁ i₂ : ι) : Prop
  := ∃ p, g.IsPathBetween i₁ i₂ p

def Graph.IsConnected (g : Graph ι α) : Prop
  := ∀ i₁ i₂, g.AreConnected i₁ i₂

end Gt3
