import Mathlib.Data.Finset.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Lemmas

import Gt3.Tree.Basic

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

end Gt3
