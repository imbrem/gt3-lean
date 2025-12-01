import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn

namespace Gt3

/-- A node or tag with a fixed number of children -/
class NumChildren (α : Type _) where
  numChildren : α → ℕ

open NumChildren

instance instNumChildrenNat : NumChildren ℕ where
  numChildren n := n

instance instNumChildrenFin {k} : NumChildren (Fin k) where
  numChildren i := i

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

instance instBinderListList : BinderList (List ℕ) where
  binderList l := l
  numChildren l := l.length

@[simp]
theorem BinderList.numChildren_binderList {α} [BinderList α] (t : α)
  : numChildren (binderList t) = numChildren t
  := by simp only [numChildren, binderList_length]

structure LenTag {Len : Type _} (α : Len → Type _) : Type _ where
  len : Len
  tag : α len

instance LenTag.instNumChildren
  {Len} {α : Len → Type _} [NumChildren Len] : NumChildren (LenTag α) where
  numChildren wc := numChildren wc.len

instance LenTag.instBinderList
  {Len} {α : Len → Type _} [BinderList Len] : BinderList (LenTag α) where
  binderList wc := binderList wc.len

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

/-- Coerce this object's tags -/
class CoeTag (α β : Type _) where
  coeTag : α → β

/-- A homomorphism on tree tags -/
class NumChildrenHom {α β : Type _} [NumChildren α] [NumChildren β]
  (f : α → β) : Prop where
  numChildren_hom : ∀ t, numChildren (f t) = numChildren t

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
  : BinderListHom (binderList (α := α)) where
  binderList_hom _ := rfl
  numChildren_hom _ := by rw [numChildren_binderList]

instance BinderListHom.instTagLen {Len : Type _} [BinderList Len] {α : Len → Type _}
  : BinderListHom (α := LenTag α) LenTag.len where
  binderList_hom _ := rfl
  numChildren_hom _ := rfl

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

end Gt3
