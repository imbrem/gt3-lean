import Gt3.Syntax.Tree.Defs.Tree

namespace Gt3

open NumChildren BinderList HasChildren


/-- A single de-Bruijn node -/
structure DNode (α : ℕ → Type _) [∀ k, BinderList (α k)] (β : ℕ → Type _) (k : ℕ) : Type _ where
  tag : α k
  children : (i :  Fin (numChildren tag)) → (β (k + getBinder tag i))

instance {α} [∀ k, BinderList (α k)] {β} {k} : BinderList (DNode α β k) where
  numChildren t := numChildren t.tag
  binderList t := binderList t.tag
  getBinder t := getBinder t.tag
  getBinder_eq t := getBinder_eq t.tag

instance {α} [∀ k, BinderList (α k)] {β} {k} : HasChildren (DNode α β k) (fun i => β (k + i)) where
  getDChild t i := t.children i

/-- A tree of de-Bruijn nodes -/
inductive DTree (α : ℕ → Type _) [∀ k, BinderList (α k)] : ℕ → Type _
  | node {k}
    (h : α k) (children : (i : Fin (numChildren h)) → DTree α (k + getBinder h i)) : DTree α k

instance {α} [∀ k, BinderList (α k)] {k} : BinderList (DTree α k) where
  numChildren | .node h _ => numChildren h
  binderList | .node h _ => binderList h
  getBinder | .node h _ => getBinder h
  getBinder_eq h i := by cases h; simp only [getBinder_eq]

instance {α} [∀ k, BinderList (α k)] {k} : HasChildren (DTree α k) (fun b => DTree α (k + b))
  where getDChild | .node _ children => children

def DNode.toTree {α} [∀ k, BinderList (α k)] {k}
  (n : DNode α (DTree α) k) : DTree α k :=
  ⟨n.tag, n.children⟩

def DTree.toNode {α} [∀ k, BinderList (α k)] {k}
  (t : DTree α k) : DNode α (DTree α) k :=
  match t with
  | .node h children => ⟨h, children⟩

@[simp]
theorem DTree.toNode_toTree {α} [∀ k, BinderList (α k)] {k}
  (t : DTree α k) : t.toNode.toTree = t
  := by cases t; rfl

@[simp]
theorem DNode.toTree_toNode {α} [∀ k, BinderList (α k)] {k}
  (n : DNode α (DTree α) k) : n.toTree.toNode = n
  := by cases n; rfl

instance DNode.Node.toTree_binderListHom {α} [∀ k, BinderList (α k)] {k} :
  BinderListHom (DNode.toTree (α := α) (k := k)) where
  numChildren_hom _ := rfl
  binderList_hom _ := rfl

instance DTree.toNode_binderListHom {α} [∀ k, BinderList (α k)] {k} :
  BinderListHom (DTree.toNode (α := α) (k := k)) where
  numChildren_hom x := by cases x; rfl
  binderList_hom x := by cases x; rfl

def Node.toD {α} [BinderList α] {β} (k)
  (n : Node α β) : DNode (fun _ => α) (fun _ => β) k :=
  ⟨n.tag, n.children⟩

def Tree.toD {α} [BinderList α] (k)
  : Tree α → DTree (fun _ => α) k
  | .node tag children => .node tag (fun i => (children i).toD _)

def DNode.toF {α} [BinderList α] {β} {k}
  (n : DNode (fun _ => α) (fun _ => β) k) : Node α β :=
  ⟨n.tag, n.children⟩

def DTree.toF {α} [BinderList α] {k}
  : DTree (fun _ => α) k → Tree α
  | .node tag children => .node tag (fun i => (children i).toF)

theorem Node.toD_toF {α} [BinderList α] {β} {k}
  (n : Node α β) : (n.toD k).toF = n
  := by cases n; rfl

theorem DNode.toF_toD {α} [BinderList α] {β} {k}
  (n : DNode (fun _ => α) (fun _ => β) k) : (n.toF).toD k = n
  := by cases n; rfl

theorem Tree.toD_toF {α} [BinderList α] {k}
  (t : Tree α) : (t.toD k).toF = t
  := by induction t generalizing k; simp only [toD, DTree.toF, *]

def DNode.mapChildren {α} [∀ n, BinderList (α n)] {β β' : ℕ → Type _} {k}
  (f : ∀ k, β k → β' k)
  (n : DNode α β k) : DNode α β' k :=
  ⟨n.tag, fun i => f _ (n.children i)⟩

end Gt3
