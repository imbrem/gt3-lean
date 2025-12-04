import Gt3.Cotree.Basic
import Gt3.Graph.Basic

namespace Gt3

open NumChildren BinderList HasChildren FlatChildren

variable {ι ι₁ ι₂ α α'} [BinderList α] [BinderList α']

def PCotree.RootFan (t : PCotree ι α) (src : ι) (trg : ι) : Prop :=
  t.ix = src ∨ src = trg

def PCotree.DominatesS (t : PCotree ι α) (srcSet : Set ι) (trg : ι) : Prop :=
  (∃ src ∈ srcSet, t.RootFan src trg)
    ∨ (srcSet ≠ ∅ ∧ ∀ p ∈ t.pathsBetween t.ix trg, ∃ src ∈ srcSet, src ∈ p)

def PCotree.Dominates (t : PCotree ι α) (src trg : ι) : Prop :=
  t.RootFan src trg ∨ ∀ p ∈ t.pathsBetween t.ix trg, src ∈ p

@[simp]
theorem PCotree.DominatesS.singleton_iff
  {t : PCotree ι α} {src trg : ι} :
  t.DominatesS {src} trg ↔ t.Dominates src trg :=
  by simp [DominatesS, Dominates]

-- TODO: A ⊆ B =(strict)=> DominateS A => DominateS (B)

-- TODO: empty set doesn't dominate things...

def PCotree.BookDominatesS (t : PCotree ι α) (srcSet : Set ι) (trg : ι) : Prop :=
  ∀ p ∈ t.pathsBetween t.ix trg, ∃ src ∈ srcSet, src ∈ (t.ix :: p)

def PCotree.BookDominates (t : PCotree ι α) (src trg : ι) : Prop :=
  ∀ p ∈ t.pathsBetween t.ix trg, src ∈ (t.ix :: p)

@[simp]
theorem PCotree.BookDominatesS.singleton_iff
  {t : PCotree ι α} {src trg : ι} :
  t.BookDominatesS {src} trg ↔ t.BookDominates src trg :=
  by simp [BookDominatesS, BookDominates]

-- BookDominate(S) ==> Dominate(S)

-- if everything is reachable from the root, BookDominate(S) <=> Dominate(S)

-- (Book)Dominate(S) is transitive

end Gt3
