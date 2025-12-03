import Mathlib.Data.List.FinRange

import Gt3.Tree.LeafTree
import Gt3.Tree.Bin

namespace Gt3

open NumChildren BinderList HasChildren Leaves

def BinTree.ofList {ℓ : Type _} (l : BinTree ℓ) : List (BinTree ℓ) → BinTree ℓ
  | [] => l
  | m :: r => .branch l (ofList m r)

def BinTree.ofLeaves {ℓ : Type _} (l : ℓ) (r : List ℓ) : BinTree ℓ
  := ofList (leaf l) (leaf <$> r)

@[simp]
theorem BinTree.leaves_ofList {ℓ : Type _} (l : BinTree ℓ) (r : List (BinTree ℓ)) :
  leaves (BinTree.ofList l r) = (leaves l) ++ (r.flatMap leaves) := by
  induction r generalizing l <;> simp [ofList, *]

@[simp]
def BinTree.leaves_ofLeaves {ℓ : Type _} (l : ℓ) (r : List ℓ) :
  leaves (BinTree.ofLeaves l r) = l :: r
  := by simp only [ofLeaves, List.map_eq_map, leaves_ofList, leaves_leaf, List.cons_append,
    List.nil_append, List.cons.injEq, true_and]; induction r <;> simp [*]

def BinTree?.ofList {ℓ : Type _} : List (BinTree? ℓ) → BinTree? ℓ
  | [] => .null
  | m :: r => .branch m (ofList r)

def BinTree?.ofLeaves {ℓ : Type _} (l : List ℓ) : BinTree? ℓ := ofList (leaf <$> l)

@[simp]
theorem BinTree?.leaves_ofList {ℓ : Type _} (r : List (BinTree? ℓ)) :
  leaves (BinTree?.ofList r) = r.flatMap leaves := by
  induction r <;> simp [ofList, *]

@[simp]
theorem BinTree?.leaves_ofLeaves {ℓ : Type _} (r : List ℓ) :
  leaves (BinTree?.ofLeaves r) = r
  := by simp only [ofLeaves, List.map_eq_map, leaves_ofList]; induction r <;> simp [*]

def BinTree.ofList? {ℓ : Type _} : List (BinTree ℓ) → WithNull (BinTree ℓ)
  | [] => .null
  | l :: r => .tag (BinTree.ofList l r)

@[simp]
theorem BinTree.ofList?_nil {ℓ : Type _} :
  BinTree.ofList? ([] : List (BinTree ℓ)) = WithNull.null := rfl

@[simp]
theorem BinTree.ofList?_cons {ℓ : Type _} (l : BinTree ℓ) (r : List (BinTree ℓ)) :
  BinTree.ofList? (l :: r) = WithNull.tag (BinTree.ofList l r) := rfl

def BinTree.ofLeaves? {ℓ : Type _} (r : List ℓ) : WithNull (BinTree ℓ) := ofList? (leaf <$> r)

@[simp]
theorem BinTree.ofLeaves?_nil {ℓ : Type _} :
  BinTree.ofLeaves? ([] : List ℓ) = WithNull.null := rfl

@[simp]
theorem BinTree.ofLeaves?_cons {ℓ : Type _} (l : ℓ) (r : List ℓ) :
  BinTree.ofLeaves? (l :: r) = WithNull.tag (BinTree.ofLeaves l r) := rfl

@[simp]
theorem BinTree.leaves_ofList? {ℓ : Type _} (r : List (BinTree ℓ)) :
  leaves (BinTree.ofList? r) = r.flatMap leaves := by cases r <;> simp [ofList? , *]

@[simp]
theorem BinTree.leaves_ofLeaves? {ℓ : Type _} (r : List ℓ) :
  leaves (BinTree.ofLeaves? r) = r := by cases r <;> simp

def LeafTree.ofLeaves {ℓ : Type _} (l : List ℓ) : LeafTree ℕ ℓ := .branch l.length (leaf ∘ l.get)

@[simp]
theorem LeafTree.leaves_ofLeaves {ℓ : Type _} (l : List ℓ) :
  leaves (ofLeaves l) = l := by
    simp only [ofLeaves, leaves_branch, Fin.flattenListTuple, numChildren]
    convert List.flatMap_pure_eq_map _ _
    rw [List.finRange_map_get]

def BinTree.ofFn {ℓ : Type _} {n : ℕ} (f : Fin (n + 1) → BinTree ℓ) : BinTree ℓ :=
  ofList (f 0) (List.ofFn (Fin.tail f))

@[simp]
theorem BinTree.leaves_ofFn {ℓ : Type _} {n : ℕ} (f : Fin (n + 1) → BinTree ℓ) :
  leaves (BinTree.ofFn f) = (List.ofFn f).flatMap leaves := by
  simp only [ofFn, leaves_ofList, List.ofFn_succ, List.flatMap_cons]
  rfl

@[simp]
def BinTree.rightFn {ℓ : Type _} {n : ℕ} (f : Fin (n + 1) → BinTree ℓ) : BinTree ℓ := match n with
  | 0 => (f 0)
  | _ + 1 => .branch (f 0) (rightFn (Fin.tail f))

@[simp]
theorem BinTree.leaves_rightFn {ℓ : Type _} {n : ℕ} (f : Fin (n + 1) → BinTree ℓ) :
  leaves (BinTree.rightFn f) = (List.ofFn f).flatMap leaves := by
  induction n <;> simp [Fin.tail, *]

@[simp]
def BinTree.leftFn {ℓ : Type _} {n : ℕ} (f : Fin (n + 1) → BinTree ℓ)
  : BinTree ℓ := match n with
  | 0 => f 0
  | n + 1 => .branch (leftFn (Fin.init f)) (f (Fin.last (n + 1)))

@[simp]
theorem BinTree.leaves_leftFn {ℓ : Type _} {n : ℕ} (f : Fin (n + 1) → BinTree ℓ) :
  leaves (BinTree.leftFn f) = (List.ofFn f).flatMap leaves := by
  induction n with
  | zero => simp
  | succ n I =>
    simp only [leftFn, leaves_branch, I]
    conv => rhs; rw [<-Fin.snoc_init_self f, Fin.snoc_eq_append, List.ofFn_fin_append]
    simp

@[simp]
def BinTree.leftFn? {ℓ : Type _} {n : ℕ} (f : Fin n → BinTree ℓ) : WithNull (BinTree ℓ) :=
  match n with
  | 0 => .null
  | _ + 1 => .tag (leftFn f)

@[simp]
theorem BinTree.leaves_leftFn? {ℓ : Type _} {n : ℕ} (f : Fin n → BinTree ℓ) :
  leaves (BinTree.leftFn? f) = (List.ofFn f).flatMap leaves := by cases n <;> simp

@[simp]
def BinTree.rightFn? {ℓ : Type _} {n : ℕ} (f : Fin n → BinTree ℓ) : WithNull (BinTree ℓ) :=
  match n with
  | 0 => .null
  | _ + 1 => .tag (rightFn f)

@[simp]
theorem BinTree.leaves_rightFn? {ℓ : Type _} {n : ℕ} (f : Fin n → BinTree ℓ) :
  leaves (BinTree.rightFn? f) = (List.ofFn f).flatMap leaves := by cases n <;> simp

@[simp]
def BinTree?.rightFn {ℓ : Type _} {n : ℕ} (f : Fin n → BinTree? ℓ) : BinTree? ℓ := match n with
  | 0 => .null
  | _ + 1 => .branch (f 0) (rightFn (Fin.tail f))

@[simp]
theorem BinTree?.leaves_rightFn {ℓ : Type _} {n : ℕ} (f : Fin n → BinTree? ℓ) :
  leaves (BinTree?.rightFn f) = (List.ofFn f).flatMap leaves := by
  induction n <;> simp [*] ; rfl

@[simp]
def BinTree?.leftFn {ℓ : Type _} {n : ℕ} (f : Fin n → BinTree? ℓ) : BinTree? ℓ := match n with
  | 0 => .null
  | n + 1 => .branch (leftFn (Fin.init f)) (f (Fin.last n))

@[simp]
theorem BinTree?.leaves_leftFn {ℓ : Type _} {n : ℕ} (f : Fin n → BinTree? ℓ) :
  leaves (BinTree?.leftFn f) = (List.ofFn f).flatMap leaves := by
  induction n with
  | zero => simp
  | succ n I =>
    simp only [leftFn, leaves_branch, I]
    conv => rhs; rw [<-Fin.snoc_init_self f, Fin.snoc_eq_append, List.ofFn_fin_append]
    simp

@[simp]
def LeafTree.leftBinTree? {ℓ} : LeafTree ℕ ℓ → BinTree? ℓ
  | .leaf l => .leaf l
  | .branch _ children => BinTree?.leftFn (fun i => leftBinTree? (children i))

theorem List.ofFn_flatMap {α β} (n : ℕ) (f : Fin n → α) (g : α → List β) :
  (List.ofFn f).flatMap g = (List.ofFn (g ∘ f)).flatten := by
  rw [
    List.ofFn_comp', List.flatMap_map, List.ofFn_comp', List.flatten_eq_flatMap, List.flatMap_map,
  ]
  simp

theorem LeafTree.leaves_leftBinTree? {ℓ} (t : LeafTree ℕ ℓ) :
  leaves (leftBinTree? t) = leaves t := by
  induction t with
  | leaf l => simp
  | branch _ children =>
    simp only [leftBinTree?, BinTree?.leaves_leftFn, List.flatMap, List.ofFn_comp', List.map_ofFn,
      leaves_branch, Fin.flattenListTuple]
    rw [List.flatten_eq_flatMap, List.ofFn_flatMap]
    simp only [Function.id_comp, List.finRange, List.map_ofFn]
    congr 2
    funext i; simp [*]

instance LeafTree.instLeafHomLeftBinTree? {ℓ}
  : LeafHom (leftBinTree? : LeafTree ℕ ℓ → BinTree? ℓ) where
  leaves_hom t := LeafTree.leaves_leftBinTree? t

@[simp]
def LeafTree.rightBinTree? {ℓ} : LeafTree ℕ ℓ → BinTree? ℓ
  | .leaf l => .leaf l
  | .branch _ children => BinTree?.rightFn (fun i => rightBinTree? (children i))

theorem LeafTree.leaves_rightBinTree? {ℓ} (t : LeafTree ℕ ℓ) :
  leaves (rightBinTree? t) = leaves t := by
  induction t with
  | leaf l => simp
  | branch _ children =>
    simp only [
      rightBinTree?, BinTree?.leaves_rightFn, List.flatMap, leaves_branch,
      Fin.flattenListTuple_eq_flatMap, List.finRange, List.map_ofFn
    ]
    congr 2
    funext i; simp [*]

instance LeafTree.instLeafHomRightBinTree? {ℓ}
  : LeafHom (rightBinTree? : LeafTree ℕ ℓ → BinTree? ℓ) where
  leaves_hom t := LeafTree.leaves_rightBinTree? t

end Gt3
