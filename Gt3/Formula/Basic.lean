import Gt3.JEq.Basic

namespace Gt3

open NumChildren BinderList CastLE

/-- A tag for a universal formula over locally-nameless syntax -/
inductive LnPi1Tag (α : ℕ → Type _) (τ : ℕ → Type _) : List ℕ → ℕ → Type _ where
  | atomic {k} (atomic : α k) : LnPi1Tag α τ [] k
  | imp {k} : LnPi1Tag α τ [0, 0] k
  | forall_lc {k} (ty : τ k) : LnPi1Tag α τ [1] k

/-- A universal formula-shaped de-Bruijn tree -/
inductive PiTree (α : List ℕ → ℕ → Type _) : ℕ → Type _ where
  | constant {k} (h : α [] k) : PiTree α k
  | quant {k} (h : α [1] k) (arg : PiTree α (k + 1)) : PiTree α k
  | binary {k} (h : α [0, 0] k) (left right : PiTree α k) : PiTree α k

def PiTree.depth {α} {k} : PiTree α k → ℕ
  | .constant _ => 0
  | .quant _ arg => arg.depth + 1
  | .binary _ left right => left.depth ⊔ right.depth + 1

/-- A universal formula over syntax -/
def LnPi1 (α : ℕ → Type _) (τ : ℕ → Type _) : ℕ → Type _ := PiTree (LnPi1Tag α τ)

@[match_pattern]
abbrev LnPi1.atomic {α τ k} (a : α k) : LnPi1 α τ k := .constant (.atomic a)

@[match_pattern]
abbrev LnPi1.imp {α τ k} : LnPi1 α τ k → LnPi1 α τ k → LnPi1 α τ k := .binary .imp

@[match_pattern]
abbrev LnPi1.forall_lc {α τ k} (ty : τ k) (body : LnPi1 α τ (k + 1)) : LnPi1 α τ k
  := .quant (.forall_lc ty) body

def LnPi1.depth {α τ k} : LnPi1 α τ k → ℕ := PiTree.depth

@[simp]
theorem LnPi1.depth_atomic {α τ k} (a : α k)
  : LnPi1.depth (LnPi1.atomic (α := α) (τ := τ) a) = 0 := rfl

@[simp]
theorem LnPi1.depth_imp {α τ k} (φ ψ : LnPi1 α τ k) :
  LnPi1.depth (LnPi1.imp φ ψ) = (LnPi1.depth φ ⊔ LnPi1.depth ψ) + 1 := rfl

@[simp]
theorem LnPi1.depth_forall_lc {α τ k} (ty : τ k) (body : LnPi1 α τ (k + 1)) :
  LnPi1.depth (LnPi1.forall_lc ty body) = LnPi1.depth body + 1 := rfl

class Lst (ι : Type _) (α : ℕ → Type _) where
  lst : ∀ {k}, ι → α (k + 1) → α k

open Lst

instance Tm.instLstString : Lst String Tm where
  lst x t := t.open x

instance Tm.instLstTm : Lst (Tm 0) Tm where
  lst a t := t.lst a

instance LnPi1Tag.instLst {ι α τ} [Lst ι α] [Lst ι τ] {bs} : Lst ι (LnPi1Tag α τ bs) where
  lst x | .atomic a => .atomic (lst x a)
        | .imp => .imp
        | .forall_lc ty => .forall_lc (lst x ty)

instance PiTree.instLst {ι α} [∀ bs, Lst ι (α bs)] : Lst ι (PiTree α) where
  lst x :=
    let rec go {k : ℕ} (t : PiTree α (k + 1)) : PiTree α k := match t with
              | .constant h => .constant (lst (k := k) x h)
              | .quant h arg => .quant (lst (k := k) x h) (go arg)
              | .binary h left right => .binary (lst x h) (go left) (go right)
    go

instance LnPi1.instLst {ι α τ} [Lst ι α] [Lst ι τ] : Lst ι (LnPi1 α τ) := PiTree.instLst

@[simp]
theorem LnPi1.lst_atomic {ι α τ} [Lst ι α] [Lst ι τ] {k} (x : ι) (a : α (k + 1))
  : lst x (LnPi1.atomic (α := α) (τ := τ) a) = LnPi1.atomic (lst x a)
  := by simp [lst, PiTree.instLst.go]

@[simp]
theorem LnPi1.lst_imp {ι α τ} [Lst ι α] [Lst ι τ] {k} (x : ι) (φ ψ : LnPi1 α τ (k + 1))
  : lst x (LnPi1.imp φ ψ) = LnPi1.imp (lst x φ) (lst x ψ)
  := by simp [lst, PiTree.instLst.go]

@[simp]
theorem LnPi1.lst_forall_lc {ι α τ} [Lst ι α] [Lst ι τ] {k} (x : ι) (ty : τ (k + 1))
    (body : LnPi1 α τ (k + 2))
  : lst x (LnPi1.forall_lc ty body) = LnPi1.forall_lc (lst x ty) (lst x body)
  := by simp [lst, PiTree.instLst.go]

@[simp]
theorem LnPi1.depth_lst {ι α τ} [Lst ι α] [Lst ι τ] {k} (x : ι) (φ : LnPi1 α τ (k + 1)) :
  LnPi1.depth (lst x φ) = LnPi1.depth φ := match φ with
  | .atomic _ => by simp
  | .imp lhs rhs => by simp [lhs.depth_lst, rhs.depth_lst]
  | .forall_lc _ body => by simp [body.depth_lst]
  termination_by LnPi1.depth φ

class ExtendCtx (κ : Type _) (ι : outParam (Type _)) (τ : Type _) where
  consCtx : κ → ι → τ → κ

open ExtendCtx

class IsTheoremIn (κ : Type _) (α : Type _) where
  isTheoremIn : κ → α → Prop

open IsTheoremIn

instance instListIsTheoremIn {κ : Type _} {α : Type _} [IsTheoremIn κ α]
  : IsTheoremIn κ (List α) where
  isTheoremIn Γ φs := ∀ φ ∈ φs, isTheoremIn Γ φ

@[simp]
theorem isTheoremIn_nil {κ : Type _} {α : Type _} [IsTheoremIn κ α]
  (Γ : κ) : isTheoremIn Γ ([] : List α) := by simp [isTheoremIn]

@[simp]
theorem isTheoremIn_cons {κ : Type _} {α : Type _} [IsTheoremIn κ α]
  (Γ : κ) (φ : α) (φs : List α) :
  isTheoremIn Γ (φ :: φs) ↔ isTheoremIn Γ φ ∧ isTheoremIn Γ φs :=
  by simp [isTheoremIn]

instance instFinsetIsTheoremIn {κ : Type _} {α : Type _} [IsTheoremIn κ α]
  : IsTheoremIn κ (Finset α) where
  isTheoremIn Γ φs := ∀ φ ∈ φs, isTheoremIn Γ φ

@[simp]
theorem isTheoremIn_empty {κ : Type _} {α : Type _} [IsTheoremIn κ α]
  (Γ : κ) : isTheoremIn Γ (∅ : Finset α) := by simp [isTheoremIn]

@[simp]
theorem isTheoremIn_insert {κ : Type _} {α : Type _} [IsTheoremIn κ α] [DecidableEq α]
  (Γ : κ) (φ : α) (φs : Finset α) :
  isTheoremIn Γ (insert φ φs) ↔ isTheoremIn Γ φ ∧ isTheoremIn Γ φs :=
  by simp [isTheoremIn]

instance instSetIsTheoremIn {κ : Type _} {α : Type _} [IsTheoremIn κ α]
  : IsTheoremIn κ (Set α) where
  isTheoremIn Γ φs := ∀ φ ∈ φs, isTheoremIn Γ φ

@[simp]
theorem isTheoremIn_set_empty {κ : Type _} {α : Type _} [IsTheoremIn κ α]
  (Γ : κ) : isTheoremIn Γ (∅ : Set α) := by simp [isTheoremIn]

@[simp]
theorem isTheoremIn_set_insert {κ : Type _} {α : Type _} [IsTheoremIn κ α]
  (Γ : κ) (φ : α) (φs : Set α) :
  isTheoremIn Γ (insert φ φs) ↔ isTheoremIn Γ φ ∧ isTheoremIn Γ φs :=
  by simp [isTheoremIn]

@[simp]
theorem isTheoremIn_union {κ : Type _} {α : Type _} [IsTheoremIn κ α]
  (Γ : κ) (φs₁ φs₂ : Set α) :
  isTheoremIn Γ (φs₁ ∪ φs₂) ↔ isTheoremIn Γ φs₁ ∧ isTheoremIn Γ φs₂ :=
  by simp only [isTheoremIn, Set.mem_union, or_imp, forall_and]

instance LnPi1.instIsTheoremIn
  {κ ι τ α} [Lst ι τ] [Lst ι α] [ExtendCtx κ ι (τ 0)] [IsTheoremIn κ (α 0)]
  : IsTheoremIn κ (LnPi1 α τ 0) where
  isTheoremIn :=
    let rec go (Γ φ) := match φ with
      | .atomic h => isTheoremIn Γ h
      | .imp φ ψ => (go Γ φ) -> (go Γ ψ)
      | .forall_lc ty body => (∃ L : Finset ι, ∀ x ∉ L, go (consCtx Γ x ty) (lst x body))
      termination_by depth φ
    go

@[simp]
theorem LnPi1.isTheoremIn_atomic
  {κ ι τ α} [Lst ι τ] [Lst ι α] [ExtendCtx κ ι (τ 0)] [IsTheoremIn κ (α 0)]
  (Γ : κ) (a : α 0) :
  isTheoremIn Γ (LnPi1.atomic (α := α) (τ := τ) a) ↔ isTheoremIn Γ a :=
  by simp [isTheoremIn, instIsTheoremIn.go]

@[simp]
theorem LnPi1.isTheoremIn_imp
  {κ ι τ α} [Lst ι τ] [Lst ι α] [ExtendCtx κ ι (τ 0)] [IsTheoremIn κ (α 0)]
  (Γ : κ) (φ ψ : LnPi1 α τ 0) :
  isTheoremIn Γ (LnPi1.imp φ ψ) ↔ (isTheoremIn Γ φ → isTheoremIn Γ ψ) :=
  by simp [isTheoremIn, instIsTheoremIn.go]

@[simp]
theorem LnPi1.isTheoremIn_forall_lc
  {κ ι τ α} [Lst ι τ] [Lst ι α] [ExtendCtx κ ι (τ 0)] [IsTheoremIn κ (α 0)]
  (Γ : κ) (ty : τ 0) (body : LnPi1 α τ 1) :
  isTheoremIn Γ (LnPi1.forall_lc ty body) ↔
    (∃ L : Finset ι, ∀ x ∉ L, isTheoremIn (consCtx Γ x ty) (lst x body)) :=
  by simp [isTheoremIn, instIsTheoremIn.go]

class AxiomSet (Φ : Type _) (κ : outParam (Type _)) (α : outParam (Type _)) : Type _ where
  getAxioms : Φ → κ → Set α
  insertAxiom : Φ → κ → α → Φ

open AxiomSet

def AxiomSet.ContextSound {Φ : Type _} {κ : Type _} {α : Type _}
  [IsTheoremIn κ α] [AxiomSet Φ κ α] (A : Φ) (k : κ) : Prop
  := isTheoremIn k (getAxioms A k)

def AxiomSet.AxiomsSound {Φ : Type _} {κ : Type _} {α : Type _}
  [IsTheoremIn κ α] [AxiomSet Φ κ α] (A : Φ) : Prop
  := ∀ k : κ, ContextSound A k

class InsertAxiomSound (Φ : Type _) (κ : outParam (Type _)) (α : outParam (Type _))
  [IsTheoremIn κ α] : Type _ extends AxiomSet Φ κ α where
  insertAxiomSound (A : Φ) :
    (∀ κ, ∀ φ ∈ getAxioms A κ, isTheoremIn κ φ) →
    ∀ κ φ, isTheoremIn κ φ → ∀ κ', ∀ φ' ∈ getAxioms (insertAxiom A κ φ) κ', isTheoremIn κ' φ'

instance InsertAxiomSound.instSet {κ α} [IsTheoremIn κ α] : InsertAxiomSound (κ → Set α) κ α where
  getAxioms Φ Γ := Φ Γ
  insertAxiom Φ Γ φ := fun Γ' => open Classical in if Γ = Γ' then insert φ (Φ Γ') else Φ Γ'
  insertAxiomSound Φ h Γ φ hφ Γ' φ' hφ' :=
    by
    split at hφ'
    case isTrue h => cases h; simp only [Set.mem_insert_iff] at hφ'; cases hφ' <;> simp [*]
    case isFalse h => apply_assumption; assumption

inductive AxiomSet.derivationSet {Φ κ ι α τ}
  [Lst ι τ] [Lst ι α] [ExtendCtx κ ι (τ 0)] [AxiomSet Φ κ (LnPi1 α τ 0)]
  : Φ → κ → Set (LnPi1 α τ 0) where
  | assumption {A φ} (Γ) (h : φ ∈ getAxioms A Γ) : derivationSet A Γ φ
  | imp_intro {A Γ φ ψ} (h : derivationSet (insertAxiom A Γ φ) Γ ψ)
    : derivationSet A Γ (LnPi1.imp φ ψ)
  | imp_elim {A Γ φ ψ} (himp : derivationSet A Γ (LnPi1.imp φ ψ)) (hφ : derivationSet A Γ φ)
    : derivationSet A Γ ψ
  | forall_lc_intro {A Γ ty φ} (L : Finset ι)
    (h : ∀ x ∉ L, derivationSet A (consCtx Γ x ty) (lst x φ))
    : derivationSet A Γ (LnPi1.forall_lc ty φ)

-- theorem AxiomSet.AxiomsSound.derivationSetSound {Φ κ ι α τ}
--   [Lst ι τ] [Lst ι α] [ExtendCtx κ ι (τ 0)] [AxiomSet Φ κ (LnPi1 α τ 0)]
--   [IsTheoremIn κ (α 0)] {A : Φ} (hA : AxiomsSound A)
--   : AxiomsSound (derivationSet A) := fun k φ =>
--   sorry

end Gt3
