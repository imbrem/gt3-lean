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
  getChild t i := t.children i

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
  where getChild | .node _ children => children

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

/-- A de-Bruijn index or a value -/
inductive Ix (α : ℕ → Type _) : ℕ → Type _
  | bv {k} (i : Fin k) : Ix α k
  | val {k} (h : α k) : Ix α k

instance {α} [∀ k, NumChildren (α k)] {k} : NumChildren (Ix α k) where
  numChildren
    | .bv _ => 0
    | .val h => numChildren h

instance {α} [∀ k, BinderList (α k)] {k} : BinderList (Ix α k) where
  binderList
    | .bv _ => []
    | .val h => binderList h
  getBinder
    | .bv _ => unreachable!
    | .val h => getBinder h
  getBinder_eq h i := by cases h <;> simp only [getBinder_eq] <;> rfl

instance {α} {β : ℕ → ℕ → Type _}
  [∀ k, BinderList (α k)] [∀ k, HasChildren (α k) (β k)] {k} : HasChildren (Ix α k) (β k) where
  getChild
    | .bv _ => fun i => i.elim0
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

def Var.map {ι ι' α α'} (f : ι → ι') (g : α → α') : Var ι α → Var ι' α'
  | .fv x => .fv (f x)
  | .val h => .val (g h)

theorem Var.map_id {ι α} (v : Var ι α) : v.map id id = v := by cases v <;> rfl

theorem Var.map_comp {ι ι' ι'' α α' α''}
  (f : ι → ι') (f' : ι' → ι'') (g : α → α') (g' : α' → α'')
  (v : Var ι α) :
  v.map (f' ∘ f) (g' ∘ g) = (v.map f g).map f' g' := by cases v <;> rfl

instance Var.instFunctor {ι} : Functor (Var ι) where
  map := Var.map id

instance Var.instLawfulFunctor {ι} : LawfulFunctor (Var ι) where
  map_const := rfl
  id_map _ := Var.map_id _
  comp_map _ _ _ := Var.map_comp id id _ _ _

instance Var.instMonad {ι} : Monad (Var ι) where
  pure := Var.val
  bind v f := match v with
    | .fv x => .fv x
    | .val h => f h

instance Var.instLawfulMonad {ι} : LawfulMonad (Var ι) where
  seqLeft_eq x y := by cases x <;> rfl
  seqRight_eq x y := by cases x <;> cases y <;> rfl
  pure_seq f x := by cases x <;> rfl
  bind_pure_comp f x := by cases x <;> rfl
  bind_assoc x f g := by cases x <;> rfl
  bind_map x f := by cases x <;> rfl
  pure_bind x f := by rfl

def Ix.map {k k' α α'}
  (f : Fin k → Fin k')
  (g : α k → α' k') : Ix α k → Ix α' k'
  | .bv i => .bv (f i)
  | .val h => .val (g h)

abbrev IxAt (k : ℕ) (α : Type _) := Ix (fun _ => α) k

abbrev IxAt.bv {k : ℕ} {α} (i : Fin k) : IxAt k α := Ix.bv i

abbrev IxAt.val {k : ℕ} {α} (h : α) : IxAt k α := Ix.val h

def IxAt.map {k k' α α'}
  (f : Fin k → Fin k')
  (g : α → α') : IxAt k α → IxAt k' α' :=
  Ix.map f g

instance IxAt.instFunctor {k} : Functor (IxAt k) where
  map := IxAt.map id

instance IxAt.instLawfulFunctor {k} : LawfulFunctor (IxAt k) where
  map_const := rfl
  id_map x := by cases x <;> rfl
  comp_map _ _ x := by cases x <;> rfl

instance IxAt.instMonad {k} : Monad (IxAt k) where
  pure := IxAt.val
  bind v f := match v with
    | .bv i => .bv i
    | .val h => f h

instance IxAt.instLawfulMonad {k} : LawfulMonad (IxAt k) where
  seqLeft_eq x y := by cases x <;> cases y <;> rfl
  seqRight_eq x y := by cases x <;> cases y <;> rfl
  pure_seq f x := by cases x <;> rfl
  bind_pure_comp f x := by cases x <;> rfl
  bind_assoc x f g := by cases x <;> rfl
  bind_map x f := by cases x <;> rfl
  pure_bind x f := by rfl

end Gt3
