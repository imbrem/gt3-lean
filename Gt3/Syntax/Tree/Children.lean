import Gt3.Syntax.Tree.Tag

namespace Gt3

open NumChildren BinderList

/-- A node equipped with a set of children of indexed type `β` -/
class HasChildren (α : Type _) [BinderList α] (β : ℕ → Type _) where
  getChild (t : α) : (i : Fin (numChildren t)) → (β (getBinder t i))

open HasChildren

class FlatChildren (α : Type _) [BinderList α] (β : Type _) extends HasChildren α (fun _ => β) where
  listChildren (t : α) : List β := List.ofFn (getChild t)
  listChildren_eq (t : α) : listChildren t = List.ofFn (getChild t) := by simp

@[ext]
class CastLE {ι : Type _} [PartialOrder ι] (α : ι → Type _) where
  castLE {i j} (h : i ≤ j) : α i → α j
  castLE_refl {i} (x : α i) : castLE (le_refl i) x = x := by simp
  castLE_castLE {i j k} (h1 : i ≤ j) (h2 : j ≤ k) (x : α i)
    : castLE h2 (castLE h1 x) = castLE (le_trans h1 h2) x := by simp

class BindCastLE {ι : Type _} [PartialOrder ι] (α : ι → Type _) [∀ n, BinderList (α n)]
  extends CastLE α where
  castLE_hom {i j} (h : i ≤ j) : BinderListHom (castLE h)
    := by simp only [CastLE.castLE]; infer_instance

attribute [simp] CastLE.castLE_refl CastLE.castLE_castLE

attribute [instance] BindCastLE.castLE_hom

instance CastLE.instConst {ι : Type _} [PartialOrder ι] (α : Type _)
  : CastLE (ι := ι) (fun _ => α) where
  castLE _ x := x

instance BindCastLE.instConst {ι : Type _} [PartialOrder ι] (α : Type _) [BinderList α]
  : BindCastLE (ι := ι) (fun _ => α) where

instance BinderListHom.instFinCastLE {i j} (h : i ≤ j) : BinderListHom (Fin.castLE h) where
  numChildren_hom _ := rfl
  binderList_hom _ := rfl

instance CastLE.instFin : CastLE Fin where
  castLE h x := Fin.castLE h x

instance BindCastLE.instFin : BindCastLE Fin where

instance CastLE.instOption {ι : Type _} [PartialOrder ι] {α : ι → Type _} [CastLE α]
  : CastLE (fun i => Option (α i)) where
  castLE h := Option.map (CastLE.castLE h)
  castLE_refl x := by cases x <;> simp
  castLE_castLE h1 h2 x := by cases x <;> simp

instance BindCastLE.instOption {ι : Type _} [PartialOrder ι] {α : ι → Type _}
  [∀ n, BinderList (α n)] [BindCastLE α]
  : BindCastLE (fun i => Option (α i)) where

instance CastLE.instSum {ι : Type _} [PartialOrder ι] {α β : ι → Type _}
  [CastLE α] [CastLE β] : CastLE (fun i => α i ⊕ β i) where
  castLE h := Sum.map (CastLE.castLE h) (CastLE.castLE h)
  castLE_refl x := by cases x <;> simp
  castLE_castLE h1 h2 x := by cases x <;> simp

instance BindCastLE.instSum {ι : Type _} [PartialOrder ι] {α β : ι → Type _}
  [∀ n, BinderList (α n)] [BindCastLE α]
  [∀ n, BinderList (β n)] [BindCastLE β]
  : BindCastLE (fun i => α i ⊕ β i) where

end Gt3
