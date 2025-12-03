import Mathlib.Data.List.FinRange

import Gt3.Tree.LeafTree
import Gt3.Tree.Bin

namespace Gt3

open NumChildren BinderList HasChildren Leaves

def BinTree.ofList {ℓ : Type _} (l : ℓ) : List ℓ → BinTree ℓ
  | [] => .leaf l
  | m :: r => .branch (.leaf l) (ofList m r)

@[simp]
def BinTree.leaves_ofList {ℓ : Type _} (l : ℓ) (r : List ℓ) :
  leaves (BinTree.ofList l r) = l :: r := by induction r generalizing l <;> simp [ofList, *]

def BinTree?.ofList {ℓ : Type _} : List ℓ → BinTree? ℓ
  | [] => .null
  | m :: r => .branch (.leaf m) (ofList r)

@[simp]
theorem BinTree?.leaves_ofList {ℓ : Type _} (r : List ℓ) :
  leaves (BinTree?.ofList r) = r := by induction r <;> simp [ofList, *]

def BinTree.ofList? {ℓ : Type _} : List ℓ → WithNull (BinTree ℓ)
  | [] => .null
  | l :: r => .tag (BinTree.ofList l r)

@[simp]
theorem BinTree.leaves_ofList? {ℓ : Type _} (r : List ℓ) :
  leaves (BinTree.ofList? r) = r := by cases r <;> simp [ofList?, *]

def LeafTree.ofList {ℓ : Type _} (l : List ℓ) : LeafTree ℕ ℓ := .branch l.length (leaf ∘ l.get)

@[simp]
theorem LeafTree.leaves_ofList {ℓ : Type _} (l : List ℓ) :
  leaves (ofList l) = l := by
    simp only [ofList, leaves_branch, Fin.flattenListTuple, numChildren]
    convert List.flatMap_pure_eq_map _ _
    rw [List.finRange_map_get]

def BinTree.ofFn {ℓ : Type _} {n : ℕ} (f : Fin (n + 1) → ℓ) : BinTree ℓ :=
  ofList (f 0) (List.ofFn (Fin.tail f))

@[simp]
theorem BinTree.leaves_ofFn {ℓ : Type _} {n : ℕ} (f : Fin (n + 1) → ℓ) :
  leaves (BinTree.ofFn f) = List.ofFn f := by
  simp only [ofFn, leaves_ofList]
  apply Eq.symm
  convert List.ofFn_cons _ _
  simp

@[simp]
def BinTree.rightFn {ℓ : Type _} {n : ℕ} (f : Fin (n + 1) → ℓ) : BinTree ℓ := match n with
  | 0 => .leaf (f 0)
  | _ + 1 => .branch (.leaf (f 0)) (rightFn (Fin.tail f))

@[simp]
theorem BinTree.leaves_rightFn {ℓ : Type _} {n : ℕ} (f : Fin (n + 1) → ℓ) :
  leaves (BinTree.rightFn f) = List.ofFn f := by
  induction n <;> simp [Fin.tail, *]

@[simp]
def BinTree.leftFn {ℓ : Type _} {n : ℕ} (f : Fin (n + 1) → ℓ) : BinTree ℓ := match n with
  | 0 => .leaf (f 0)
  | n + 1 => .branch (leftFn (Fin.init f)) (.leaf (f (Fin.last (n + 1))))

@[simp]
theorem BinTree.leaves_leftFn {ℓ : Type _} {n : ℕ} (f : Fin (n + 1) → ℓ) :
  leaves (BinTree.leftFn f) = List.ofFn f := by
  induction n with
  | zero => simp
  | succ n I =>
    simp only [leftFn, leaves_branch, leaves_leaf, I]
    conv => rhs; rw [<-Fin.snoc_init_self f, Fin.snoc_eq_append, List.ofFn_fin_append]
    simp

@[simp]
def BinTree.leftFn? {ℓ : Type _} {n : ℕ} (f : Fin n → ℓ) : WithNull (BinTree ℓ) :=
  match n with
  | 0 => .null
  | _ + 1 => .tag (leftFn f)

@[simp]
theorem BinTree.leaves_leftFn? {ℓ : Type _} {n : ℕ} (f : Fin n → ℓ) :
  leaves (BinTree.leftFn? f) = List.ofFn f := by cases n <;> simp

@[simp]
def BinTree.rightFn? {ℓ : Type _} {n : ℕ} (f : Fin n → ℓ) : WithNull (BinTree ℓ) :=
  match n with
  | 0 => .null
  | _ + 1 => .tag (rightFn f)

@[simp]
theorem BinTree.leaves_rightFn? {ℓ : Type _} {n : ℕ} (f : Fin n → ℓ) :
  leaves (BinTree.rightFn? f) = List.ofFn f := by cases n <;> simp

@[simp]
def BinTree?.rightFn {ℓ : Type _} {n : ℕ} (f : Fin n → ℓ) : BinTree? ℓ := match n with
  | 0 => .null
  | _ + 1 => .branch (.leaf (f 0)) (rightFn (Fin.tail f))

@[simp]
theorem BinTree?.leaves_rightFn {ℓ : Type _} {n : ℕ} (f : Fin n → ℓ) :
  leaves (BinTree?.rightFn f) = List.ofFn f := by
  induction n <;> simp [*] ; rfl

@[simp]
def BinTree?.leftFn {ℓ : Type _} {n : ℕ} (f : Fin n → ℓ) : BinTree? ℓ := match n with
  | 0 => .null
  | n + 1 => .branch (leftFn (Fin.init f)) (.leaf (f (Fin.last n)))

@[simp]
theorem BinTree?.leaves_leftFn {ℓ : Type _} {n : ℕ} (f : Fin n → ℓ) :
  leaves (BinTree?.leftFn f) = List.ofFn f := by
  induction n with
  | zero => simp
  | succ n I =>
    simp only [leftFn, leaves_branch, leaves_leaf, I]
    conv => rhs; rw [<-Fin.snoc_init_self f, Fin.snoc_eq_append, List.ofFn_fin_append]
    simp

end Gt3
