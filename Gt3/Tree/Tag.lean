import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn

namespace Gt3

/-- A node or tag with a fixed number of children -/
class NumChildren (α : Type _) where
  numChildren : α → ℕ

open NumChildren

/-- A node or tag with a fixed binding structure -/
class BinderList (α : Type _) extends NumChildren α where
  binderList : α → List ℕ
  getBinder : (t : α) → Fin (numChildren t) → ℕ := fun t i => (binderList t)[i]!
  binderList_length : ∀ t, (binderList t).length = numChildren t
    := by intro t; (try cases t) <;> (try simp [binderList]) <;> rfl
  getBinder_eq : ∀ (t : α) (i : Fin (numChildren t)), getBinder t i = (binderList t)[i]!
    := by intro t i; (try cases t) <;> (try simp) <;> (try simp [getBinder]) <;> rfl

attribute [simp] BinderList.binderList_length

/-- Get the `n`th binder of a node or tag -/
def BinderList.getBinder! {α} [BinderList α] (t : α) (i : ℕ) : ℕ := (binderList t)[i]!

open BinderList

instance instBinderListNat : BinderList ℕ where
  numChildren n := n
  binderList n := List.replicate n 0
  getBinder _ _ := 0
  getBinder_eq n i := Eq.symm <| by have h : i < n := i.prop; simp [*]

instance instBinderListFin {k} : BinderList (Fin k) where
  numChildren i := i
  binderList i := List.replicate (i.val) 0
  getBinder _ _ := 0
  getBinder_eq i j := Eq.symm <| by have h : j.val < i.val := j.prop; simp [*]

instance instBinderListList : BinderList (List ℕ) where
  binderList l := l
  numChildren l := l.length

@[simp]
theorem BinderList.numChildren_binderList {α} [BinderList α] (t : α)
  : numChildren (binderList t) = numChildren t
  := by simp only [numChildren, binderList_length]

/-- Get this object's tag -/
class GetTag (α : Type _) [BinderList α] (τ : outParam (Type _)) [BinderList τ] where
  getTag : α → τ
  binderList_getTag : ∀ t, binderList (getTag t) = binderList t

instance instGetTagNat : GetTag ℕ ℕ where
  getTag n := n
  binderList_getTag _ := rfl

instance instGetTagList : GetTag (List ℕ) (List ℕ) where
  getTag l := l
  binderList_getTag _ := rfl

open GetTag

structure LenTag {Len : Type _} (α : Len → Type _) : Type _ where
  len : Len
  tag : α len

instance LenTag.instNumChildren
  {Len} {α : Len → Type _} [NumChildren Len] : NumChildren (LenTag α) where
  numChildren wc := numChildren wc.len

instance LenTag.instBinderList
  {Len} {α : Len → Type _} [BinderList Len] : BinderList (LenTag α) where
  binderList wc := binderList wc.len
  getBinder wc := getBinder wc.len
  getBinder_eq wc i := getBinder_eq wc.len i

instance instGetTagLenTag {Len} {α : Len → Type _}
  [BinderList Len] [∀ l, BinderList (α l)]
  : GetTag (LenTag α) (LenTag α) where
  getTag wc := wc
  binderList_getTag _ := rfl

structure NumChildren.WithLen
  (Len : Type _ := ℕ) [NumChildren Len] (α : Type _) [NumChildren α] : Type _
  extends LenTag (fun _ : Len => α)
  where
  numChildren_tag : numChildren tag = numChildren len

instance WithLen.instNumChildren
  (Len : Type _ := ℕ) [NumChildren Len] {α} [NumChildren α]
  : NumChildren (WithLen Len α) where
  numChildren wc := numChildren wc.len

abbrev WithLen.len {Len : Type _} [NumChildren Len] {α} [NumChildren α]
  (wc : WithLen Len α) : Len := wc.len

abbrev WithLen.tag {Len : Type _} [NumChildren Len] {α} [NumChildren α]
  (wc : WithLen Len α) : α := wc.tag

structure BinderList.WithBind
  (Len : Type _ := ℕ) [BinderList Len] (α : Type _) [BinderList α] : Type _
  extends WithLen Len α
  where
  binderList_tag : binderList tag = binderList len

instance WithBind.instBinderList
  (Len : Type _ := ℕ) [BinderList Len] {α} [BinderList α]
  : BinderList (WithBind Len α) where
  numChildren wb := numChildren wb.len
  binderList wb := binderList wb.len

abbrev WithBind.len {Len : Type _} [BinderList Len] {α} [BinderList α]
  (wb : WithBind Len α) : Len := wb.len

abbrev WithBind.tag {Len : Type _} [BinderList Len] {α} [BinderList α]
  (wb : WithBind Len α) : α := wb.tag

def NumChildren.HasLen
  {Len : Type _} [NumChildren Len] (α : Type _) [NumChildren α] (len : Len) : Type _
  := { t : α // numChildren t = numChildren len }

instance HasLen.instNumChildren {Len : Type _} [NumChildren Len] {α} [NumChildren α] {len : Len}
  : NumChildren (HasLen α len) where
  numChildren _ := numChildren len

def BinderList.HasBind
  {Len : Type _} [BinderList Len] (α : Type _) [BinderList α] (bs : Len) : Type _
  := { t : α // binderList t = binderList bs }

instance HasBind.instBinderList {Len : Type _} [BinderList Len] {α} [BinderList α] {len : Len}
  : BinderList (HasBind α len) where
  numChildren _ := numChildren len
  binderList _ := binderList len
  getBinder _ := getBinder len
  getBinder_eq _ i := getBinder_eq len i

/-- A homomorphism on tree tags -/
class NumChildrenHom {α β : Type _} [NumChildren α] [NumChildren β]
  (f : α → β) : Prop where
  numChildren_hom : ∀ t, numChildren (f t) = numChildren t

attribute [simp] NumChildrenHom.numChildren_hom

instance NumChildrenHom.id {α} [NumChildren α] : NumChildrenHom (fun x : α => x) where
  numChildren_hom _ := rfl

theorem NumChildrenHom.of_numChildren_comp {α β : Type _} [NumChildren α] [NumChildren β]
  {f : α → β} (h : numChildren ∘ f = numChildren)
  : NumChildrenHom f where numChildren_hom := congrFun h

theorem NumChildrenHom.numChildren_comp {α β : Type _} [NumChildren α] [NumChildren β]
  {f : α → β} (hf : NumChildrenHom f)
  : numChildren ∘ f = numChildren := funext hf.numChildren_hom

theorem NumChildrenHom.comp {α β γ : Type _} [NumChildren α] [NumChildren β] [NumChildren γ]
  {f : α → β} {g : β → γ}
  (hf : NumChildrenHom f) (hg : NumChildrenHom g)
  : NumChildrenHom (g ∘ f) where
  numChildren_hom t := by rw [Function.comp_apply, hg.numChildren_hom, hf.numChildren_hom]

instance NumChildrenHom.instComp {α β γ : Type _} [NumChildren α] [NumChildren β] [NumChildren γ]
  {f : α → β} {g : β → γ}
  [hf : NumChildrenHom f] [hg : NumChildrenHom g]
  : NumChildrenHom (g ∘ f) := NumChildrenHom.comp hf hg

instance NumChildrenHom.instNumChildren {α : Type _} [NumChildren α]
  : NumChildrenHom (numChildren (α := α)) where
  numChildren_hom _ := rfl

instance NumChildrenHom.instTagLen {Len : Type _} [NumChildren Len] {α : Len → Type _}
  : NumChildrenHom (α := LenTag α) LenTag.len where
  numChildren_hom _ := rfl

instance NumChildrenHom.instTagWithLen {Len : Type _} [NumChildren Len] {α : Type _} [NumChildren α]
  : NumChildrenHom (α := WithLen Len α) WithLen.len where
  numChildren_hom _ := rfl

instance NumChildrenHom.instTagWithBind {Len : Type _} [BinderList Len] {α : Type _} [BinderList α]
  : NumChildrenHom (α := WithBind Len α) WithBind.len where
  numChildren_hom _ := rfl

/-- A homomorphism on bind-tree tags -/
class BinderListHom {α β : Type _} [BinderList α] [BinderList β]
  (f : α → β) : Prop extends NumChildrenHom f where
  binderList_hom : ∀ t, binderList (f t) = binderList t

attribute [simp] BinderListHom.binderList_hom

instance BinderListHom.id {α} [BinderList α] : BinderListHom (fun x : α => x) where
  binderList_hom _ := rfl

theorem BinderListHom.mk' {α β : Type _} [BinderList α] [BinderList β]
  {f : α → β} (binderList_hom : ∀ t, binderList (f t) = binderList t)
  : BinderListHom f where
  binderList_hom := binderList_hom
  numChildren_hom t := by rw [<-binderList_length, binderList_hom, binderList_length]

theorem BinderListHom.of_binderList_comp {α β : Type _} [BinderList α] [BinderList β]
  {f : α → β} (h : binderList ∘ f = binderList)
  : BinderListHom f := mk' <| congrFun h

theorem BinderListHom.binderList_comp {α β : Type _} [BinderList α] [BinderList β]
  {f : α → β} (hf : BinderListHom f)
  : binderList ∘ f = binderList := funext hf.binderList_hom

theorem BinderListHom.comp {α β γ : Type _} [BinderList α] [BinderList β] [BinderList γ]
  {f : α → β} {g : β → γ}
  (hf : BinderListHom f) (hg : BinderListHom g)
  : BinderListHom (g ∘ f)
  := mk' fun _ => by rw [Function.comp_apply, hg.binderList_hom, hf.binderList_hom]

instance BinderListHom.instComp {α β γ : Type _} [BinderList α] [BinderList β] [BinderList γ]
  {f : α → β} {g : β → γ}
  [hf : BinderListHom f] [hg : BinderListHom g]
  : BinderListHom (g ∘ f) := BinderListHom.comp hf hg

instance BinderListHom.instBinderList {α : Type _} [BinderList α]
  : BinderListHom (binderList (α := α))
  := BinderListHom.mk' fun _ => rfl

instance BinderListHom.instGetTag {α τ} [BinderList α] [BinderList τ]
  [hf : GetTag α τ] : BinderListHom (getTag (α := α))
  := BinderListHom.mk' hf.binderList_getTag

instance BinderListHom.instTagLen {Len : Type _} [BinderList Len] {α : Len → Type _}
  : BinderListHom (α := LenTag α) LenTag.len
  := BinderListHom.mk' fun _ => rfl

instance BinderListHom.instTagWithBind {Len : Type _} [BinderList Len] {α : Type _} [BinderList α]
  : BinderListHom (α := WithBind Len α) WithBind.len where
  binderList_hom _ := rfl

instance instNumChildrenOption {α} [NumChildren α] : NumChildren (Option α) where
  numChildren
    | .none => 0
    | .some a => numChildren a

instance instBinderListOption {α} [BinderList α] : BinderList (Option α) where
  binderList
    | .none => []
    | .some a => binderList a
  getBinder
    | .none => Fin.elim0
    | .some a => getBinder a
  getBinder_eq
    | .none => fun i => i.elim0
    | .some a => getBinder_eq a

instance NumChildrenHom.instSome {α} [NumChildren α] : NumChildrenHom (Option.some (α := α)) where
  numChildren_hom _ := rfl

instance BinderListHom.instSome {α} [BinderList α] : BinderListHom (Option.some (α := α)) where
  binderList_hom _ := rfl

instance NumChildrenHom.instOptionMap {α β} [NumChildren α] [NumChildren β]
  {f : α → β} [hf : NumChildrenHom f]
  : NumChildrenHom (Option.map f) where
  numChildren_hom
    | .none => rfl
    | .some a => hf.numChildren_hom a

instance BinderListHom.instOptionMap {α β} [BinderList α] [BinderList β]
  {f : α → β} [hf : BinderListHom f]
  : BinderListHom (Option.map f) where
  binderList_hom
    | .none => rfl
    | .some a => hf.binderList_hom a

instance NumChildrenHom.instOptionBind {α β} [NumChildren α] [NumChildren β]
  {f : α → Option β} [hf : NumChildrenHom f]
  : NumChildrenHom (fun a : Option α => a.bind f) where
  numChildren_hom
    | .none => rfl
    | .some a => hf.numChildren_hom a

instance BinderListHom.instOptionBind {α β} [BinderList α] [BinderList β]
  {f : α → Option β} [hf : BinderListHom f]
  : BinderListHom (fun a : Option α => a.bind f) where
  binderList_hom
    | .none => rfl
    | .some a => hf.binderList_hom a

instance instNumChildrenSum {α β} [NumChildren α] [NumChildren β]
  : NumChildren (Sum α β) where
  numChildren
    | .inl a => numChildren a
    | .inr b => numChildren b

instance instBinderListSum {α β} [BinderList α] [BinderList β]
  : BinderList (Sum α β) where
  binderList
    | .inl a => binderList a
    | .inr b => binderList b
  getBinder
    | .inl a => getBinder a
    | .inr b => getBinder b
  getBinder_eq
    | .inl a => getBinder_eq a
    | .inr b => getBinder_eq b

instance NumChildrenHom.instSumInl {α β} [NumChildren α] [NumChildren β]
  : NumChildrenHom (Sum.inl (α := α) (β := β)) where
  numChildren_hom _ := rfl

instance BinderListHom.instSumInl {α β} [BinderList α] [BinderList β]
  : BinderListHom (Sum.inl (α := α) (β := β)) where
  binderList_hom _ := rfl

instance NumChildrenHom.instSumInr {α β} [NumChildren α] [NumChildren β]
  : NumChildrenHom (Sum.inr (α := α) (β := β)) where
  numChildren_hom _ := rfl

instance BinderListHom.instSumInr {α β} [BinderList α] [BinderList β]
  : BinderListHom (Sum.inr (α := α) (β := β)) where
  binderList_hom _ := rfl

instance NumChildrenHom.instSumMap {α₁ α₂ β₁ β₂}
  [NumChildren α₁] [NumChildren α₂] [NumChildren β₁] [NumChildren β₂]
  {f₁ : α₁ → β₁} {f₂ : α₂ → β₂}
  [hf₁ : NumChildrenHom f₁] [hf₂ : NumChildrenHom f₂]
  : NumChildrenHom (Sum.map f₁ f₂) where
  numChildren_hom
    | .inl a => hf₁.numChildren_hom a
    | .inr b => hf₂.numChildren_hom b

instance BinderListHom.instSumMap {α₁ α₂ β₁ β₂}
  [BinderList α₁] [BinderList α₂] [BinderList β₁] [BinderList β₂]
  {f₁ : α₁ → β₁} {f₂ : α₂ → β₂}
  [hf₁ : BinderListHom f₁] [hf₂ : BinderListHom f₂]
  : BinderListHom (Sum.map f₁ f₂) where
  binderList_hom
    | .inl a => hf₁.binderList_hom a
    | .inr b => hf₂.binderList_hom b

instance NumChildrenHom.instSumElim {α β γ} [NumChildren α] [NumChildren β] [NumChildren γ]
  {f : α → γ} {g : β → γ}
  [hf : NumChildrenHom f] [hg : NumChildrenHom g]
  : NumChildrenHom (Sum.elim f g) where
  numChildren_hom
    | .inl a => hf.numChildren_hom a
    | .inr b => hg.numChildren_hom b

instance BinderListHom.instSumElim {α β γ} [BinderList α] [BinderList β] [BinderList γ]
  {f : α → γ} {g : β → γ}
  [hf : BinderListHom f] [hg : BinderListHom g]
  : BinderListHom (Sum.elim f g) where
  binderList_hom
    | .inl a => hf.binderList_hom a
    | .inr b => hg.binderList_hom b

instance NumChildrenHom.instSumSwap {α β} [NumChildren α] [NumChildren β]
  : NumChildrenHom (Sum.swap (α := α) (β := β)) where
  numChildren_hom h := by cases h <;> rfl

instance BinderListHom.instSumSwap {α β} [BinderList α] [BinderList β]
  : BinderListHom (Sum.swap (α := α) (β := β)) where
  binderList_hom h := by cases h <;> rfl

/-- A node or tag which has a constant number of binders -/
class BoundValues (α : Type _) extends BinderList α where
  boundValues : α → ℕ
  getBinder_eq_boundValues : ∀ (t : α) (i : Fin (numChildren t)), getBinder t i = boundValues t

open BoundValues

/-- A node or tag which does not introduce binders -/
class NonBinding (α : Type _) [BoundValues α] : Prop where
  boundValues_eq_zero : ∀ (t : α) , boundValues t = 0

@[simp]
theorem NonBinding.getBinder_eq_zero {α} [BoundValues α] [NonBinding α]
  (t : α) (i : Fin (numChildren t)) : getBinder t i = 0 :=
  by rw [getBinder_eq_boundValues, NonBinding.boundValues_eq_zero t]

instance instBoundValuesNat : BoundValues ℕ where
  boundValues _ := 0
  getBinder_eq_boundValues _ _ := rfl

instance instNonBindingNat : NonBinding ℕ where
  boundValues_eq_zero _ := rfl

-- instance instNonBindingFin {k} : NonBinding (Fin k) where
--   boundValues_eq_zero _ := rfl

-- open NonBinding

-- instance instNonBindingOption {α} [BinderList α] [NonBinding α]
--   : NonBinding (Option α) where
--   getBinder_eq_zero
--     | .none => fun i => i.elim0
--     | .some a => getBinder_eq_zero a

-- instance instNonBindingSum {α β} [BinderList α] [BinderList β] [NonBinding α] [NonBinding β]
--   : NonBinding (Sum α β) where
--   getBinder_eq_zero
--     | .inl a => getBinder_eq_zero a
--     | .inr b => getBinder_eq_zero b

-- instance instNonBindingLenTag {Len : Type _} [BinderList Len] [NonBinding Len] {α : Len → Type _}
--   : NonBinding (LenTag α) where
--   getBinder_eq_zero wc i := getBinder_eq_zero wc.len i

-- theorem NonBinding.binderList_eq_replicate {α} [BinderList α] [NonBinding α]
--   (t : α) : binderList t = List.replicate (numChildren t) 0 := by
--   apply List.ext_getElem
--   · simp
--   · intro i h h'
--     convert NonBinding.getBinder_eq_zero t ⟨i, (by convert h; simp)⟩
--     · rw [getBinder_eq]
--       simp only [Fin.getElem!_fin, List.getElem!_eq_getElem?_getD, Nat.default_eq_zero]
--       rw [List.getElem?_eq_getElem]
--       · simp
--       exact h
--     · simp

-- instance BinderListHom.instNumChildren {α : Type _} [BinderList α] [NonBinding α]
--   : BinderListHom (numChildren (α := α)) where
--   binderList_hom _ := by simp [binderList_eq_replicate, NumChildrenHom.numChildren_hom]

end Gt3
