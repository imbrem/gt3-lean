import Gt3.Tree.Node

namespace Gt3

open NumChildren BinderList HasChildren

inductive WithLeaf (ι : Type _) (ℓ : Type _) : Type _
  | branch (b : ι) : WithLeaf ι ℓ
  | leaf (l : ℓ) : WithLeaf ι ℓ

instance WithLeaf.instNumChildren {ι} [NumChildren ι] {ℓ} : NumChildren (WithLeaf ι ℓ) where
  numChildren
    | .branch b => numChildren b
    | .leaf _ => 0

instance WithLeaf.instBinderList {ι} [BinderList ι] {ℓ} : BinderList (WithLeaf ι ℓ) where
  binderList
    | .branch b => binderList b
    | .leaf _ => []
  getBinder
    | .branch b => getBinder b
    | .leaf _ => unreachable!
  getBinder_eq h := by intro i; cases h <;> simp only [getBinder_eq] <;> rfl

instance WithLeaf.instHasChildren
  {ι β} [BinderList ι] [HasChildren ι β] {ℓ} : HasChildren (WithLeaf ι ℓ) β where
  getDChild
    | .branch b => getDChild b
    | .leaf _ => fun i => i.elim0

instance WithLeaf.instFlatChildren
  {ι β} [BinderList ι] [FlatChildren ι β] {ℓ} : FlatChildren (WithLeaf ι ℓ) β where

def WithLeaf.mapBranch {ι₁ ι₂ ℓ} (f : ι₁ → ι₂) (t : WithLeaf ι₁ ℓ) : WithLeaf ι₂ ℓ :=
  match t with
  | .branch b => .branch (f b)
  | .leaf l => .leaf l

def WithLeaf.mapLeaf {ι ℓ₁ ℓ₂} (f : ℓ₁ → ℓ₂) (t : WithLeaf ι ℓ₁) : WithLeaf ι ℓ₂ :=
  match t with
  | .branch b => .branch b
  | .leaf l => .leaf (f l)

inductive WithLeaf.liftRel {ι₁ ι₂ ℓ₁ ℓ₂}
  (branch : ι₁ → ι₂ → Prop) (leaf : ℓ₁ → ℓ₂ → Prop)
  : WithLeaf ι₁ ℓ₁ → WithLeaf ι₂ ℓ₂ → Prop
  | branch {b₁ b₂} (h : branch b₁ b₂)
    : liftRel branch leaf (WithLeaf.branch b₁) (WithLeaf.branch b₂)
  | leaf {l₁ l₂} (h : leaf l₁ l₂)
    : liftRel branch leaf (WithLeaf.leaf l₁) (WithLeaf.leaf l₂)

class Leaves (τ : Type _) (ℓ : outParam (Type _)) where
  leaves : τ → List ℓ

open Leaves

instance WithLeaf.instLeaves {ι} {ℓ} : Leaves (WithLeaf ι ℓ) ℓ where
  leaves
    | .branch _ => []
    | .leaf l => [l]

instance Sum.instLeaves {τ₁ τ₂ ℓ}
  [Leaves τ₁ ℓ] [Leaves τ₂ ℓ] : Leaves (τ₁ ⊕ τ₂) ℓ where
  leaves
    | .inl t1 => leaves t1
    | .inr t2 => leaves t2

class LeafHom {τ₁ τ₂ ℓ} [Leaves τ₁ ℓ] [Leaves τ₂ ℓ] (f : τ₁ → τ₂) where
  leaves_hom : ∀ t : τ₁, leaves (f t) = leaves t

attribute [simp] LeafHom.leaves_hom

instance LeafHom.id {τ ℓ} [Leaves τ ℓ] : LeafHom (fun t => t : τ → τ) where
  leaves_hom _ := rfl

instance LeafHom.comp {τ₁ τ₂ τ₃ ℓ}
  [Leaves τ₁ ℓ] [Leaves τ₂ ℓ] [Leaves τ₃ ℓ]
  {f : τ₁ → τ₂} {g : τ₂ → τ₃}
  [LeafHom f] [LeafHom g] : LeafHom (g ∘ f) where
  leaves_hom t := by simp

end Gt3
