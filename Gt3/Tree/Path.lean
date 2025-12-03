import Mathlib.Data.Finset.Lattice.Fold

import Gt3.Tree.Basic

namespace Gt3

open NumChildren BinderList HasChildren FlatChildren GetNode GetTag

structure Step (α : Type _) [NumChildren α] : Type _ where
  tag : α
  ix : Fin (numChildren tag)

def Tree.depth {α : Type _} [NumChildren α] : Tree α → ℕ
  | .node _ children => (List.ofFn (fun i => depth (children i) + 1)).foldr max 0

structure Path (α : Type _) (β : Type _ := α) : Type _ where
  steps : List α
  stop : β

@[match_pattern]
def Path.nil {α β : Type _} (b : β) : Path α β := { steps := [], stop := b }

def Path.cons {α β : Type _} (step : α) (p : Path α β) : Path α β :=
  { steps := step :: p.steps, stop := p.stop }

def Path.length {α β : Type _} (p : Path α β) : ℕ := p.steps.length

@[simp]
theorem Path.length_nil {α β : Type _} (b : β) : (Path.nil (α := α) b).length = 0 := rfl

@[simp]
theorem Path.length_cons {α β : Type _} (step : α) (p : Path α β) :
  (Path.cons step p).length = p.length + 1 := by simp [Path.length, Path.cons]

@[simp]
theorem Path.cons_ne_nil {α β : Type _} (step : α) (tail : Path α β) (b : β)
  : Path.cons step tail ≠ Path.nil b :=
  by intro h; cases h

@[induction_eliminator]
def Path.inductionOn {α β : Type _} {motive : Path α β → Sort _}
  (nil : ∀ b, motive (.nil b))
  (cons : ∀ (step : α) (p : Path α β), motive p → motive (Path.cons step p))
  (p : Path α β) : motive p :=
  match p with
  | .mk [] stop => nil stop
  | .mk (head::steps) stop =>
    cons head ⟨steps, stop⟩ (inductionOn nil cons ⟨steps, stop⟩)

inductive GetNode.getPaths {α τ : Type _}
  [BinderList α] [BinderList τ] [GetTag α τ] [FlatChildren α α]
  : α → Set (Path (Step τ) τ) where
  | nil {t : α} : getPaths t (.nil (getTag t))
  | cons
      (a : α) (ix : Fin (numChildren (getTag a))) (tail : Path (Step τ) τ)
      (htail : tail ∈ getPaths (α := α) (getChild a (ix.cast (by simp))))
      : getPaths a (.cons (Step.mk (getTag a) ix) tail)

@[simp]
theorem GetNode.getTag_mem_getPaths {α τ : Type _}
  [BinderList α] [BinderList τ] [GetTag α τ] [FlatChildren α α]
  (t : α) : (.nil (getTag t)) ∈ GetNode.getPaths (α := α) t :=
  GetNode.getPaths.nil

inductive GetNode.getTraces {α τ : Type _}
  [BinderList α] [BinderList τ] [GetTag α τ] [FlatChildren α α]
  : α → Set (List τ) where
  | nil {t : α} : getTraces t []
  | cons
      (a : α) (ix : Fin (numChildren (getTag a))) (tail : List τ)
      (htail : tail ∈ getTraces (α := α) (getChild a (ix.cast (by simp))))
      : getTraces a ((getTag a) :: tail)

attribute [simp] getTraces.nil

theorem GetNode.getPaths_node_subset {α τ : Type _} [BinderList α]
  (t : α) [BinderList α] [BinderList τ] [GetTag α τ] [FlatChildren α α]
  : insert (.nil (getTag t)) (⋃ i : Fin (numChildren (getTag t)),
    { .cons (Step.mk (getTag t) i) p | p ∈ getPaths (getChild (β := α) t (i.cast (by simp))) })
    ⊆ getPaths t
  := by
  intro path
  simp only [Set.mem_insert_iff, Set.mem_iUnion, Set.mem_setOf_eq]
  intro hpath
  cases hpath with
  | inl hpath => cases hpath; simp
  | inr hpath =>
    revert hpath
    simp only [forall_exists_index, and_imp]
    intro i tail htail heq
    cases heq
    apply GetNode.getPaths.cons
    exact htail

theorem GetNode.subset_getPaths_node {α τ : Type _} [BinderList α]
  (t : α) [BinderList α] [BinderList τ] [GetTag α τ] [FlatChildren α α]
  : getPaths t
    ⊆ insert (.nil (getTag t)) (⋃ i : Fin (numChildren (getTag t)),
      { Path.cons (Step.mk (getTag t) i) p
        | p ∈ getPaths (getChild (β := α) t (i.cast (by simp))) })
  := by
  intro path hpath
  cases hpath
  · simp
  case cons htail =>
    simp only [Set.mem_insert_iff, Path.cons_ne_nil, Set.mem_iUnion, Set.mem_setOf_eq, false_or]
    constructor
    constructor
    constructor
    · exact htail
    rfl

theorem GetNode.getPaths_node {α τ : Type _} [BinderList α]
  (t : α) [BinderList α] [BinderList τ] [GetTag α τ] [FlatChildren α α]
  : getPaths t
    = insert (.nil (getTag t)) (⋃ i : Fin (numChildren (getTag t)),
      { Path.cons (Step.mk (getTag t) i) p
        | p ∈ getPaths (getChild (β := α) t (i.cast (by simp))) })
  := le_antisymm (subset_getPaths_node t) (getPaths_node_subset t)

-- TODO: tags are obviously the same by `insert`


-- theorem GetNode.getPaths_eq_union {α τ : Type _} [BinderList α]
--   {t t' : α} [BinderList α] [BinderList τ] [GetTag α τ] [FlatChildren α α]
--   (h : getPaths t = getPaths t')
--   : (⋃ i : Fin (numChildren (getTag t)),
--       { Path.cons (Step.mk (getTag t) i) p
--         | p ∈ getPaths (getChild (β := α) t (i.cast (by simp))) })
--   = (⋃ i : Fin (numChildren (getTag t')),
--       { Path.cons (Step.mk (getTag t') i) p
--         | p ∈ getPaths (getChild (β := α) t' (i.cast (by simp))) })
--   := by
--   sorry

-- theorem GetNode.getPaths_eq_tag {α τ : Type _} [BinderList α]
--   {t t' : α} [BinderList α] [BinderList τ] [GetTag α τ] [FlatChildren α α]
--   (h : getPaths t = getPaths t')
--   : getTag t = getTag t'
--   := by
--   have hu := getPaths_eq_union h
--   simp only [Set.ext_iff, Set.mem_iUnion, Set.mem_setOf_eq] at hu
--   sorry

theorem Tree.getPaths_node_subset {α : Type _} [BinderList α]
  (tag : α) (children : Fin (numChildren tag) → Tree α)
  : insert (Path.nil tag)
    (⋃ i : Fin (numChildren tag), { Path.cons (Step.mk tag i) p | p ∈ getPaths (children i) })
    ⊆ getPaths (Tree.node tag children)
  := GetNode.getPaths_node_subset (Tree.node tag children)

-- theorem Tree.subset_getPaths_node {α : Type _} [BinderList α]
--   (tag : α) (children : Fin (numChildren tag) → Tree α)
--   : getPaths (Tree.node tag children)
--     ⊆ insert [] (⋃ i : Fin (numChildren tag), { Step.mk tag i :: p | p ∈ getPaths (children i) })
--   := GetNode.subset_getPaths_node (Tree.node tag children)

theorem Tree.getPaths_node {α : Type _} [BinderList α]
  (tag : α) (children : Fin (numChildren tag) → Tree α)
  : getPaths (Tree.node tag children)
    = insert (Path.nil tag)
      (⋃ i : Fin (numChildren tag), { Path.cons (Step.mk tag i) p | p ∈ getPaths (children i) })
  := GetNode.getPaths_node (Tree.node tag children)

-- def Tree.getPaths_inj {α} [BinderList α] {t t' : Tree α} (h : getPaths t = getPaths t')
--   : t = t' := by
--   induction t generalizing t' with
--   | mk tag children I =>
--     cases t' with
--     | mk tag' children' =>
--       have h_union := GetNode.getPaths_eq_union h
--       sorry

def Tree.getStep {α} [NumChildren α] [DecidableEq α] (t : Tree α) (s : Step α) : Option (Tree α)
  := if h : t.tag = s.tag then
      some (t.children (s.ix.cast (by rw [h])))
    else
      none

def Tree.getPath {α} [NumChildren α] [DecidableEq α] (t : Tree α) : List (Step α) → Option (Tree α)
  | [] => some t
  | s :: ss => (Tree.getStep t s).bind (fun t => Tree.getPath t ss)

end Gt3
