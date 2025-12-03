import Gt3.Tree.Basic
import Gt3.Tree.WithNull
import Gt3.Tree.WithLeaf

namespace Gt3

open NumChildren BinderList HasChildren Leaves

inductive BinOnly : Type
  | bin

instance BinOnly.instNumChildren : NumChildren BinOnly where
  numChildren _ := 2

@[simp]
theorem BinOnly.numChildren_eq (b : BinOnly) : numChildren b = 2 := rfl

instance BinOnly.instBinderList : BinderList BinOnly where
  binderList _ := [0, 0]
  getBinder _ _ := 0
  getBinder_eq _ := by intro i; simp only [numChildren_eq] at i; cases i; grind

abbrev BinTag := WithNull BinOnly

@[match_pattern]
abbrev BinTag.bin : BinTag := .tag .bin

@[match_pattern]
abbrev BinTag.null : BinTag := WithNull.null

@[cases_eliminator, induction_eliminator]
def BinTag.casesOn {motive : BinTag → Sort _}
  (h_bin : motive .bin)
  (h_null : motive .null)
  : (t : BinTag) → motive t
  | .tag .bin => h_bin
  | .null     => h_null

inductive BinTree (ℓ : Type _) : Type _
  | leaf (l : ℓ) : BinTree ℓ
  | branch (lhs rhs : BinTree ℓ) : BinTree ℓ

instance BinTree.instMonad : Monad BinTree where
  pure := BinTree.leaf
  bind t f :=
    let rec go
      | .leaf l => f l
      | .branch lhs rhs => .branch (go lhs) (go rhs)
    go t

@[simp]
theorem BinTree.map_leaf {ℓ ℓ'} (l : ℓ) (f : ℓ → ℓ') :
  f <$> (leaf l) = leaf (f l) := rfl

@[simp]
theorem BinTree.map_branch {ℓ ℓ'} (lhs rhs : BinTree ℓ) (f : ℓ → ℓ') :
  f <$> (branch lhs rhs) = branch (f <$> lhs) (f <$> rhs) := rfl

@[simp]
theorem BinTree.bind_leaf {ℓ ℓ'} (l : ℓ) (f : ℓ → BinTree ℓ') :
  (leaf l) >>= f = f l := rfl

@[simp]
theorem BinTree.bind_branch {ℓ ℓ'} (lhs rhs : BinTree ℓ) (f : ℓ → BinTree ℓ') :
  (branch lhs rhs) >>= f = branch (lhs >>= f) (rhs >>= f) := rfl

instance BinTree.instLawfulMonad : LawfulMonad BinTree := LawfulMonad.mk'
  (id_map := fun x => by induction x <;> simp [*])
  (pure_bind := fun x f => by simp [pure])
  (bind_assoc := fun x f g => by induction x <;> simp [*])

instance BinTree.instLeaves {ℓ : Type _} : Leaves (BinTree ℓ) ℓ where
  leaves :=
    let rec go
    | .leaf l => [l]
    | .branch lhs rhs => (go lhs) ++ (go rhs)
    go

@[simp]
theorem BinTree.leaves_leaf {ℓ} (l : ℓ) :
  leaves (BinTree.leaf l) = [l] := rfl

@[simp]
theorem BinTree.leaves_branch {ℓ} (lhs rhs : BinTree ℓ) :
  leaves (BinTree.branch lhs rhs) = (leaves lhs) ++ (leaves rhs) := rfl

theorem BinTree.leaves_bind {ℓ ℓ'} (t : BinTree ℓ) (f : ℓ → BinTree ℓ') :
  leaves (t >>= f) = ((leaves t).flatMap (fun l => leaves (f l))) := by
  induction t <;> simp [*]

theorem BinTree.leaves_map {ℓ ℓ'} (t : BinTree ℓ) (f : ℓ → ℓ') :
  leaves (f <$> t) = (leaves t).map f := by
  induction t <;> simp [*]

instance BinTree.assocSetoid {ℓ} : Setoid (BinTree ℓ) where
  r := fun t1 t2 => leaves t1 = leaves t2
  iseqv :=
    ⟨fun _ => rfl,
     fun h => h.symm,
     fun h1 h2 => h1.trans h2⟩

def BinTree? (ℓ : Type _) : Type _ := BinTree (WithNull ℓ)

@[match_pattern]
def BinTree?.branch {ℓ} (lhs rhs : BinTree? ℓ) : BinTree? ℓ :=
  BinTree.branch lhs rhs

@[match_pattern]
def BinTree?.leaf {ℓ} (l : ℓ) : BinTree? ℓ := BinTree.leaf (WithNull.tag l)

@[match_pattern]
def BinTree?.null {ℓ} : BinTree? ℓ := BinTree.leaf (WithNull.null)

@[induction_eliminator]
def BinTree?.inductionOn {ℓ} {motive : BinTree? ℓ → Sort _}
  (branch : ∀ lhs rhs, motive lhs → motive rhs → motive (BinTree?.branch lhs rhs))
  (leaf : ∀ l : ℓ, motive (BinTree?.leaf l))
  (null : motive (BinTree?.null))
  : ∀ t : BinTree? ℓ, motive t
  | .branch lhs rhs
    => branch lhs rhs (inductionOn branch leaf null lhs) (inductionOn branch leaf null rhs)
  | .leaf l => leaf l
  | .null => null

@[cases_eliminator]
def BinTree?.casesOn {ℓ} {motive : BinTree? ℓ → Sort _}
  (branch : ∀ lhs rhs, motive (BinTree?.branch lhs rhs))
  (leaf : ∀ l : ℓ, motive (BinTree?.leaf l))
  (null : motive (BinTree?.null))
  : ∀ t : BinTree? ℓ, motive t
  | .branch lhs rhs => branch lhs rhs
  | .leaf l => leaf l
  | .null => null

def BinTree?.toBinTree {ℓ} (t : BinTree? ℓ) : BinTree (WithNull ℓ) := t

@[simp]
theorem BinTree?.toBinTree_leaf {ℓ} (l : ℓ) :
  toBinTree (.leaf l) = .leaf (.tag l) := rfl

@[simp]
theorem BinTree?.toBinTree_null {ℓ} :
  toBinTree (ℓ := ℓ) (.null) = .leaf (.null) := rfl

@[simp]
theorem BinTree?.toBinTree_branch {ℓ} (lhs rhs : BinTree? ℓ) :
  toBinTree (.branch lhs rhs) = .branch (toBinTree lhs) (toBinTree rhs) := rfl

def BinTree.filter {ℓ} (t : BinTree (WithNull ℓ)) : BinTree? ℓ := t

@[simp]
theorem BinTree.filter_leaf_tag {ℓ} (l : ℓ) :
  filter (.leaf (.tag l)) = .leaf l := rfl

@[simp]
theorem BinTree.filter_leaf_null {ℓ} :
  filter (ℓ := ℓ) (.leaf (.null)) = .null := rfl

@[simp]
theorem BinTree.filter_branch {ℓ} (lhs rhs : BinTree (WithNull ℓ)) :
  filter (.branch lhs rhs) = .branch (filter lhs) (filter rhs) := rfl

@[simp]
theorem BinTree?.toBinTree_filter {ℓ} (t : BinTree? ℓ) :
  (toBinTree t).filter = t := rfl

@[simp]
theorem BinTree.filter_toBinTree {ℓ} (t : BinTree (WithNull ℓ)) :
  (filter t).toBinTree = t := rfl

instance BinTree?.instMonad : Monad BinTree? where
  pure := BinTree?.leaf
  bind t f :=
    let rec go
      | .leaf l => f l
      | .null => .null
      | .branch lhs rhs => .branch (go lhs) (go rhs)
    go t

@[simp]
theorem BinTree?.map_leaf {ℓ ℓ'} (l : ℓ) (f : ℓ → ℓ') :
  f <$> (BinTree?.leaf l) = BinTree?.leaf (f l) := rfl

@[simp]
theorem BinTree?.map_null {ℓ ℓ'} (f : ℓ → ℓ') :
  f <$> (BinTree?.null) = BinTree?.null := rfl

@[simp]
theorem BinTree?.map_branch {ℓ ℓ'} (lhs rhs : BinTree? ℓ) (f : ℓ → ℓ') :
  f <$> (BinTree?.branch lhs rhs) = BinTree?.branch (f <$> lhs) (f <$> rhs) := rfl

@[simp]
theorem BinTree?.bind_leaf {ℓ ℓ'} (l : ℓ) (f : ℓ → BinTree? ℓ') :
  (BinTree?.leaf l) >>= f = f l := rfl

@[simp]
theorem BinTree?.bind_null {ℓ ℓ'} (f : ℓ → BinTree? ℓ') :
  (BinTree?.null) >>= f = BinTree?.null := rfl

@[simp]
theorem BinTree?.bind_branch {ℓ ℓ'} (lhs rhs : BinTree? ℓ) (f : ℓ → BinTree? ℓ') :
  (BinTree?.branch lhs rhs) >>= f = BinTree?.branch (lhs >>= f) (rhs >>= f) := rfl

instance BinTree?.instLawfulMonad : LawfulMonad BinTree? := LawfulMonad.mk'
  (id_map := fun x => by induction x <;> simp [*])
  (pure_bind := fun x f => by simp [pure])
  (bind_assoc := fun x f g => by induction x <;> simp [*])

instance BinTree?.instLeaves {ℓ : Type _} : Leaves (BinTree? ℓ) ℓ where
  leaves := let rec go
    | .leaf l => [l]
    | .null  => []
    | .branch lhs rhs => (go lhs) ++ (go rhs)
    go

@[simp]
theorem BinTree?.leaves_leaf {ℓ} (l : ℓ) : leaves (BinTree?.leaf l) = [l] := rfl

@[simp]
theorem BinTree?.leaves_null {ℓ} : leaves (BinTree?.null (ℓ := ℓ)) = [] := rfl

@[simp]
theorem BinTree?.leaves_branch {ℓ} (lhs rhs : BinTree? ℓ) :
  leaves (BinTree?.branch lhs rhs) = (leaves lhs) ++ (leaves rhs) := rfl

theorem BinTree?.leaves_bind {ℓ ℓ'} (t : BinTree? ℓ) (f : ℓ → BinTree? ℓ') :
  leaves (t >>= f) = ((leaves t).flatMap (fun l => leaves (f l))) := by
  induction t <;> simp [*]

theorem BinTree?.leaves_map {ℓ ℓ'} (t : BinTree? ℓ) (f : ℓ → ℓ') :
  leaves (f <$> t) = (leaves t).map f := by
  induction t <;> simp [*]

theorem BinTree?.toBinTree_leaves_filterMap {ℓ} (t : BinTree? ℓ) :
  (leaves t.toBinTree).filterMap id = leaves t := by
  induction t <;> simp [WithNull.tag, WithNull.null, *]

theorem BinTree.filter_leaves {ℓ} (t : BinTree (WithNull ℓ)) :
  (leaves t.filter) = (leaves t).filterMap id := by
  induction t with
  | leaf l => cases l <;> rfl
  | branch lhs rhs => simp [*]

instance BinTree?.assocSetoid {ℓ} : Setoid (BinTree? ℓ) where
  r := fun t1 t2 => leaves t1 = leaves t2
  iseqv :=
    ⟨fun _ => rfl,
     fun h => h.symm,
     fun h1 h2 => h1.trans h2⟩

def BinTree?.toBinTree? {ℓ} : BinTree? ℓ → WithNull (BinTree ℓ)
  | .leaf l => .tag (.leaf l)
  | .null => .null
  | .branch lhs rhs => do
      let lhs ← toBinTree? lhs
      let rhs ← toBinTree? rhs
      .tag (.branch lhs rhs)

def BinTree.toBinTree? {ℓ} (t : BinTree ℓ) : BinTree? ℓ := (WithNull.tag <$> t).filter

instance WithNull.instLeaves {τ ℓ} [Leaves τ ℓ] : Leaves (WithNull τ) ℓ where
  leaves
  | .null => []
  | .tag t => leaves t

@[simp]
theorem WithNull.leaves_null {τ ℓ} [Leaves τ ℓ] :
  leaves (null : WithNull τ) = [] := rfl

@[simp]
theorem WithNull.leaves_tag {τ ℓ} [Leaves τ ℓ] (t : τ) :
  leaves (tag t) = leaves t := rfl

def BinTree' (ℓ : Type _) : Type _ := Tree (WithLeaf BinOnly ℓ)

def BinTree?' (ℓ : Type _) : Type _ := Tree (WithLeaf BinTag ℓ)

end Gt3
