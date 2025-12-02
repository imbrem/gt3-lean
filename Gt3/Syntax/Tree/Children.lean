import Gt3.Syntax.Tree.Tag

namespace Gt3

open NumChildren BinderList

/-- A node equipped with a set of children of indexed type `β` -/
class HasChildren (α : Type _) [BinderList α] (β : ℕ → Type _) where
  getDChild (t : α) : (i : Fin (numChildren t)) → (β (getBinder t i))

open HasChildren

class FlatChildren (α : Type _) [BinderList α] (β : Type _) extends HasChildren α (fun _ => β) where
  getChild (t : α) : (i : Fin (numChildren t)) → β := getDChild t
  getChild_eq (t : α) (i : Fin (numChildren t)) : getChild t i = getDChild t i := by intros; rfl
  listChildren (t : α) : List β := List.ofFn (getChild t)
  listChildren_eq (t : α) : listChildren t = List.ofFn (getChild t) := by simp

end Gt3
