import Mathlib.Data.Finset.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Lemmas

import Gt3.Tree.Basic
import Gt3.Tree.WithLeaf

namespace Gt3

open NumChildren BinderList HasChildren Leaves

inductive LeafTree (ι : Type _) [NumChildren ι] (ℓ : Type _) : Type _
  | leaf (l : ℓ) : LeafTree ι ℓ
  | branch (b : ι) (children : Fin (numChildren b) → LeafTree ι ℓ) : LeafTree ι ℓ

instance LeafTree.instNumChildren {ι} [NumChildren ι] {ℓ} : NumChildren (LeafTree ι ℓ) where
  numChildren
    | .leaf _ => 0
    | .branch b _ => numChildren b

instance LeafTree.instBinderList {ι} [BinderList ι] {ℓ} : BinderList (LeafTree ι ℓ) where
  binderList
    | .leaf _ => []
    | .branch b _ => binderList b
  getBinder
    | .leaf _ => unreachable!
    | .branch b _ => getBinder b
  getBinder_eq h := by intro i; cases h <;> simp only [getBinder_eq] <;> rfl

instance LeafTree.instFlatChildren
  {ι} [BinderList ι] {ℓ} : FlatChildren (LeafTree ι ℓ) (LeafTree ι ℓ) where
  getDChild
    | .leaf _ => fun i => i.elim0
    | .branch b children => children

instance LeafTree.instMonad {ι} [NumChildren ι] : Monad (LeafTree ι) where
  pure l := .leaf l
  bind t f :=
    let rec go
      | .leaf l => f l
      | .branch b children => .branch b (fun i => go (children i))
    go t

@[simp]
theorem LeafTree.map_leaf {ι} [NumChildren ι] {ℓ ℓ'} (f : ℓ → ℓ') (l : ℓ) :
  f <$> LeafTree.leaf (ι := ι) l = LeafTree.leaf (f l) := rfl

@[simp]
theorem LeafTree.map_branch {ι} [NumChildren ι] {ℓ ℓ'} (f : ℓ → ℓ') (b : ι)
  (children : Fin (numChildren b) → LeafTree ι ℓ) :
  f <$> LeafTree.branch (ι := ι) b children =
  LeafTree.branch b (fun i => f <$> children i) := rfl

@[simp]
theorem LeafTree.bind_leaf {ι} [NumChildren ι] {ℓ ℓ'} (l : ℓ)
  (f : ℓ → LeafTree ι ℓ') :
  (LeafTree.leaf l) >>= f = f l := rfl

@[simp]
theorem LeafTree.bind_branch {ι} [NumChildren ι] {ℓ ℓ'} (b : ι)
  (children : Fin (numChildren b) → LeafTree ι ℓ)
  (f : ℓ → LeafTree ι ℓ') :
  (LeafTree.branch b children) >>= f =
  LeafTree.branch b (fun i => children i >>= f) := rfl

instance LeafTree.instLawfulMonad {ι} [NumChildren ι] : LawfulMonad (LeafTree ι)
  := LawfulMonad.mk'
    (id_map := fun x => by induction x <;> simp [*])
    (pure_bind := fun x f => by simp [pure])
    (bind_assoc := fun x f g => by induction x <;> simp [*])

@[simp]
def Fin.flattenListTuple {n α} (a : Fin n → List α) : List α :=
  (List.finRange n).flatMap a

theorem Fin.flattenListTuple_eq_flatMap {n α} (a : Fin n → List α) :
  Fin.flattenListTuple a = (List.finRange n).flatMap a := rfl

-- theorem Fin.flattenListTuple_eq_foldr_ofFn {n α} (a : Fin n → List α) :
--   Fin.flattenListTuple a = (List.ofFn a).foldr (· ++ ·) [] := by
--   induction n with
--   | zero => rfl
--   | succ n I =>
--     simp only [
--       flattenListTuple, List.finRange, List.ofFn_succ, List.flatMap_cons, List.foldr_cons]
--     rw [<-I]
--     simp

-- theorem Fin.flattenListTuple_eq_ofFn {n α} (a : Fin n → List α) :
--   Fin.flattenListTuple a = (List.ofFn a).flatten := by sorry

instance LeafTree.instLeaves {ι} [NumChildren ι] {ℓ} : Leaves (LeafTree ι ℓ) ℓ where
  leaves :=
    let rec go
      | .leaf l => [l]
      | .branch _ children => Fin.flattenListTuple (fun i => go (children i))
    go

@[simp]
theorem LeafTree.leaves_leaf {ι} [NumChildren ι] {ℓ} (l : ℓ) :
  leaves (LeafTree.leaf (ι := ι) l) = [l] := rfl

@[simp]
theorem LeafTree.leaves_branch {ι} [NumChildren ι] {ℓ}
  (b : ι) (children : Fin (numChildren b) → LeafTree ι ℓ) :
  leaves (LeafTree.branch (ι := ι) b children) =
  Fin.flattenListTuple (leaves ∘ children) := rfl

theorem LeafTree.leaves_bind {ι} [NumChildren ι] {ℓ ℓ'}
  (t : LeafTree ι ℓ) (f : ℓ → LeafTree ι ℓ') :
  leaves (t >>= f) = (leaves t).flatMap (leaves ∘ f) := by
  induction t generalizing f
  <;> simp only [
    leaves_leaf, List.flatMap_singleton, Function.comp_apply, bind_leaf, bind_branch,
    leaves_branch, Fin.flattenListTuple, List.flatMap_assoc, *]
  congr
  funext i
  simp [*]

theorem LeafTree.leaves_map {ι} [NumChildren ι] {ℓ ℓ'}
  (f : ℓ → ℓ') (t : LeafTree ι ℓ) :
  leaves (f <$> t) = (leaves t).map f
  := by rw [map_eq_pure_bind, leaves_bind, List.map_eq_flatMap]; rfl

/-- Two leaf trees are equivalent if they both associate to the same flat list of leaves -/
instance LeafTree.assocSetoid {ι} [NumChildren ι] {ℓ} : Setoid (LeafTree ι ℓ) where
  r := fun t1 t2 => leaves t1 = leaves t2
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

theorem LeafTree.assocSetoid_def {ι} [NumChildren ι] {ℓ}
  {t1 t2 : LeafTree ι ℓ} : t1 ≈ t2 ↔ leaves t1 = leaves t2 := by rfl

theorem LeafTree.assocSetoid_fun_def {ι} [NumChildren ι] {ℓ ℓ'}
  {f1 f2 : ℓ → LeafTree ι ℓ'} : f1 ≈ f2 ↔ leaves ∘ f1 = leaves ∘ f2 := by rw [funext_iff]; rfl

@[simp]
theorem LeafTree.leaf_equiv_iff {ι} [NumChildren ι] {ℓ}
  (l1 l2 : ℓ) :
  (LeafTree.leaf (ι := ι) l1) ≈ (LeafTree.leaf (ι := ι) l2) ↔ l1 = l2 := by
  simp [assocSetoid_def]

theorem LeafTree.branch_equiv_iff {ι} [NumChildren ι] {ℓ}
  (b1 b2 : ι)
  (children1 : Fin (numChildren b1) → LeafTree ι ℓ)
  (children2 : Fin (numChildren b2) → LeafTree ι ℓ) :
  (branch (ι := ι) b1 children1) ≈ (branch (ι := ι) b2 children2) ↔
  Fin.flattenListTuple (leaves ∘ children1) = Fin.flattenListTuple (leaves ∘ children2)
  := by rfl

theorem funext_heq_iff_heq_ty {α} {β γ : α → Type _} (h : β ≍ γ)
  (f : (i : α) → β i) (g : (i : α) → γ i) : f ≍ g ↔ (∀i, f i ≍ g i) :=
  by cases h ; simp [funext_iff]

theorem Fin.heq_dep_fun_iff_cast {k l} (h : k = l) {α : Fin k → Type _} {β : Fin l → Type _}
  (hαβ : ∀ i, α i = β (i.cast h))
  (f : (i : Fin k) → α i) (g : (j : Fin l) → β j) : f ≍ g ↔ (∀i, f i ≍ g (i.cast h)) := by
  cases h
  rw [funext_heq_iff_heq_ty]
  · rfl
  · simp only [heq_eq_eq]; exact funext hαβ

theorem Fin.heq_fun_iff_cast {k l} (h : k = l) {α}
  (f : (i : Fin k) → α) (g : (j : Fin l) → α) : f ≍ g ↔ (∀i, f i = g (i.cast h))
  := by cases h; simp [funext_iff]

theorem LeafTree.branch_equiv_congr {ι} [NumChildren ι] {ℓ}
  (b1 b2 : ι)
  {children1 : Fin (numChildren b1) → LeafTree ι ℓ}
  {children2 : Fin (numChildren b2) → LeafTree ι ℓ}
  (hchildren : numChildren b1 = numChildren b2)
  (h : ∀ i, children1 i ≈ children2 (i.cast hchildren)) :
  (branch (ι := ι) b1 children1) ≈ (branch (ι := ι) b2 children2) := by
  simp only [assocSetoid_def, leaves_branch, Fin.flattenListTuple]
  congr 1
  · rw [hchildren]
  · rw [Fin.heq_fun_iff_cast (h := hchildren)]
    intro i
    exact h i
  · rw [hchildren]

theorem LeafTree.bind_equiv_congr {ι} [NumChildren ι] {ℓ ℓ'}
  {t t' : LeafTree ι ℓ} (ht : t ≈ t') {f f' : ℓ → LeafTree ι ℓ'} (hf : f ≈ f')
  : t >>= f ≈ t' >>= f'
  := by simp [assocSetoid_def, leaves_bind, assocSetoid_fun_def.mp hf, assocSetoid_def.mp ht]

theorem LeafTree.fmap_equiv_congr {ι} [NumChildren ι] {ℓ ℓ'}
  {t t' : LeafTree ι ℓ} (f : ℓ → ℓ') (ht : t ≈ t')
  : f <$> t ≈ f <$> t'
  := by rw [assocSetoid_def, leaves_map, leaves_map, ht]

def LeafTree' (ι : Type _) [NumChildren ι] (ℓ : Type _) := Tree (WithLeaf ι ℓ)

@[match_pattern]
abbrev LeafTree'.leaf {ι} [NumChildren ι]
  {ℓ} (l : ℓ) (children : Fin 0 → LeafTree' ι ℓ := Fin.elim0) : LeafTree' ι ℓ :=
  .node (.leaf l) children

theorem LeafTree'.leaf_elim0 {ι} [NumChildren ι] {ℓ} (l : ℓ) (children : Fin 0 → LeafTree' ι ℓ)
  : LeafTree'.leaf (ι := ι) l children = LeafTree'.leaf (ι := ι) l := by
  simp only [leaf]; congr; ext i; exact i.elim0

@[match_pattern]
def LeafTree'.branch {ι} [NumChildren ι] {ℓ}
  (b : ι) (children : Fin (numChildren b) → LeafTree' ι ℓ) : LeafTree' ι ℓ :=
  .node (.branch b) children

instance LeafTree'.instNumChildren {ι} [NumChildren ι] {ℓ} : NumChildren (LeafTree' ι ℓ)
  := Tree.instNumChildren

instance LeafTree'.instBinderList {ι} [BinderList ι] {ℓ} : BinderList (LeafTree' ι ℓ)
  := Tree.instBinderList

instance LeafTree'.instFlatChildren
  {ι} [BinderList ι] {ℓ} : FlatChildren (LeafTree' ι ℓ) (LeafTree' ι ℓ)
  := Tree.instFlatChildren

@[induction_eliminator]
def LeafTree'.inductionOn {ι} [NumChildren ι] {ℓ} {motive : LeafTree' ι ℓ → Sort _}
  (h_leaf : ∀ l, motive (leaf (ι := ι) l))
  (h_branch : ∀ b children, (∀ i, motive (children i)) → motive (branch (ι := ι) b children))
  : ∀ t : LeafTree' ι ℓ, motive t
  | .leaf l children => leaf_elim0 l children ▸ h_leaf l
  | .branch b children =>
    h_branch b children (fun i => LeafTree'.inductionOn h_leaf h_branch (children i))

@[cases_eliminator]
def LeafTree'.casesOn {ι} [NumChildren ι] {ℓ} {motive : LeafTree' ι ℓ → Sort _}
  (h_leaf : ∀ l, motive (leaf (ι := ι) l))
  (h_branch : ∀ b children, motive (branch (ι := ι) b children))
  : ∀ t : LeafTree' ι ℓ, motive t
  | .leaf l children => leaf_elim0 l children ▸ h_leaf l
  | .branch b children => h_branch b children

@[simp]
def LeafTree'.toLeafTree {ι} [NumChildren ι] {ℓ}
  : LeafTree' ι ℓ → LeafTree ι ℓ
  | .leaf l _ => .leaf l
  | .branch b children => .branch b (fun i => toLeafTree (children i))

@[simp]
def LeafTree.toLeafTree' {ι} [NumChildren ι] {ℓ}
  : LeafTree ι ℓ → LeafTree' ι ℓ
  | .leaf l => .leaf l
  | .branch b children => .branch b (fun i => toLeafTree' (children i))

theorem LeafTree'.toLeafTree_toLeafTree' {ι} [NumChildren ι] {ℓ}
  (t : LeafTree' ι ℓ) : (toLeafTree t).toLeafTree' = t := by induction t <;> simp [*]

theorem LeafTree.toLeafTree'_toLeafTree {ι} [NumChildren ι] {ℓ}
  (t : LeafTree ι ℓ) : (toLeafTree' t).toLeafTree = t := by induction t <;> simp [*]

instance LeafTree.toLeafTree'BinderListHom {ι} [BinderList ι] {ℓ} :
  BinderListHom (LeafTree.toLeafTree' (ι := ι) (ℓ := ℓ))
  := BinderListHom.mk' fun t => by cases t <;> rfl

instance LeafTree'.toLeafTreeBinderListHom {ι} [BinderList ι] {ℓ} :
  BinderListHom (LeafTree'.toLeafTree (ι := ι) (ℓ := ℓ))
  := BinderListHom.mk' fun t => by cases t <;> rfl

end Gt3
