import Gt3.Tree.Tag

namespace Gt3

@[ext]
class CastLE {ι : Type _} [PartialOrder ι] (α : ι → Type _) where
  castLE {i j} (h : i ≤ j) : α i → α j
  castLE_refl {i} (x : α i) : castLE (le_refl i) x = x := by simp
  castLE_castLE {i j k} (h1 : i ≤ j) (h2 : j ≤ k) (x : α i)
    : castLE h2 (castLE h1 x) = castLE (le_trans h1 h2) x := by simp

open CastLE

abbrev CastLE.castSucc {α : ℕ → Type _} [CastLE α] {k : ℕ} : α k → α (k + 1) :=
  castLE (Nat.le_succ k)

class BindCastLE {ι : Type _} [PartialOrder ι] (α : ι → Type _) [∀ n, BinderList (α n)]
  extends CastLE α where
  castLE_binderHom {i j} (h : i ≤ j) : BinderListHom (castLE h)
    := by simp only [CastLE.castLE]; infer_instance

class Erase {ι : Type _} (α : ι → Type _) (β : Type _) where
  erase : ∀ i, α i → β

open Erase

attribute [simp] CastLE.castLE_refl CastLE.castLE_castLE

attribute [instance] BindCastLE.castLE_binderHom

instance CastLE.instConst {ι : Type _} [PartialOrder ι] (α : Type _)
  : CastLE (ι := ι) (fun _ => α) where
  castLE _ x := x

instance BindCastLE.instConst {ι : Type _} [PartialOrder ι] (α : Type _) [BinderList α]
  : BindCastLE (ι := ι) (fun _ => α) where

instance BinderListHom.instFinCastLE {i j} (h : i ≤ j) : BinderListHom (Fin.castLE h) where
  numChildren_hom _ := rfl
  binderList_hom _ := rfl

instance CastLE.instFin : CastLE Fin where
  castLE h x := Fin.castLE h x

instance BindCastLE.instFin : BindCastLE Fin where

instance Erase.instFin : Erase Fin ℕ where
  erase _ x := x.val

instance CastLE.instOption {ι : Type _} [PartialOrder ι] {α : ι → Type _} [CastLE α]
  : CastLE (fun i => Option (α i)) where
  castLE h := Option.map (CastLE.castLE h)
  castLE_refl x := by cases x <;> simp
  castLE_castLE h1 h2 x := by cases x <;> simp

instance BindCastLE.instOption {ι : Type _} [PartialOrder ι] {α : ι → Type _}
  [∀ n, BinderList (α n)] [BindCastLE α]
  : BindCastLE (fun i => Option (α i)) where

instance Erase.instOption {ι : Type _} {α : ι → Type _} {β} [Erase α β]
  : Erase (fun i => Option (α i)) (Option β) where
  erase i x := Option.map (erase i) x

instance CastLE.instSum {ι : Type _} [PartialOrder ι] {α β : ι → Type _}
  [CastLE α] [CastLE β] : CastLE (fun i => α i ⊕ β i) where
  castLE h := Sum.map (CastLE.castLE h) (CastLE.castLE h)
  castLE_refl x := by cases x <;> simp
  castLE_castLE h1 h2 x := by cases x <;> simp

instance BindCastLE.instSum {ι : Type _} [PartialOrder ι] {α β : ι → Type _}
  [∀ n, BinderList (α n)] [BindCastLE α]
  [∀ n, BinderList (β n)] [BindCastLE β]
  : BindCastLE (fun i => α i ⊕ β i) where

instance Erase.instSum {ι : Type _} {α β : ι → Type _} {α' β' : Type _}
  [Erase α α'] [Erase β β'] : Erase (fun i => α i ⊕ β i) (α' ⊕ β') where
  erase i x := Sum.map (erase i) (erase i) x

class CastHom {ι : Type _} [PartialOrder ι] {α β : ι → Type _}
  [CastLE α] [CastLE β] (f : ∀ i, α i → β i) : Prop where
  castLE_hom {i j} (h : i ≤ j) (x : α i)
    : f j (CastLE.castLE h x) = CastLE.castLE h (f i x) := by
    simp [CastLE.castLE, f]

class EraseHom {ι : Type _} {α β : ι → Type _} (γ : Type _)
  [Erase α γ] [Erase β γ] (f : ∀ i, α i → β i) : Prop where
  erase_hom i (x : α i) : (erase i (f i x) : γ) = erase i x := by simp [erase, f]

attribute [simp] EraseHom.erase_hom

instance CastHom.instId {ι : Type _} [PartialOrder ι] {α : ι → Type _}
  [CastLE α] : CastHom (f := fun i => id (α := α i)) where
  castLE_hom _ _ := rfl

instance CastHom.instComp {ι : Type _} [PartialOrder ι] {α β γ : ι → Type _}
  [CastLE α] [CastLE β] [CastLE γ]
  {f : ∀ i, α i → β i} {g : ∀ i, β i → γ i}
  [CastHom f] [CastHom g]
  : CastHom (f := fun i => (g i) ∘ (f i)) where
  castLE_hom h x := by simp [CastHom.castLE_hom]

instance EraseHom.instId {ι : Type _} {α : ι → Type _} {β} [Erase α β]
  : EraseHom β (fun i => id (α := α i)) where
  erase_hom _ _ := rfl

instance EraseHom.instComp {ι : Type _} {α β γ : ι → Type _} {δ : Type _}
  [Erase α δ] [Erase β δ] [Erase γ δ]
  {f : ∀ i, α i → β i} {g : ∀ i, β i → γ i}
  [EraseHom δ f] [EraseHom δ g]
  : EraseHom δ (fun i => (g i) ∘ (f i)) where
  erase_hom i x := by simp

instance CastHom.instConst {ι : Type _} [PartialOrder ι] {α : Type _} {β : Type _}
  (f : α → β) : CastHom (α := fun _ => α) (β := fun _ => β) (fun _ : ι => f) where
  castLE_hom _ _ := rfl

instance CastHom.instOptionMap {ι : Type _} [PartialOrder ι] {α β : ι → Type _}
  [CastLE α] [CastLE β] {f : ∀ i, α i → β i}
  [CastHom f]
  : CastHom (f := fun i => Option.map (f i)) where
  castLE_hom h x := by cases x <;> simp [CastLE.castLE, CastHom.castLE_hom]

instance EraseHom.instOptionMap {ι : Type _} {α β : ι → Type _} {γ : Type _}
  [Erase α γ] [Erase β γ] {f : ∀ i, α i → β i}
  [EraseHom γ f]
  : EraseHom (Option γ) (fun i => Option.map (f i)) where
  erase_hom i x := by cases x <;> simp [erase, EraseHom.erase_hom]

instance CastHom.instOptionSome {ι : Type _} [PartialOrder ι] {α : ι → Type _}
  [CastLE α] : CastHom (f := fun i => Option.some (α := α i)) where
  castLE_hom h x := by simp [CastLE.castLE]

instance CastHom.instSumInl {ι : Type _} [PartialOrder ι] {α β : ι → Type _}
  [CastLE α] [CastLE β] : CastHom (f := fun i => Sum.inl (α := α i) (β := β i)) where
  castLE_hom h x := by simp [CastLE.castLE]

instance CastHom.instSumInr {ι : Type _} [PartialOrder ι] {α β : ι → Type _}
  [CastLE α] [CastLE β] : CastHom (f := fun i => Sum.inr (α := α i) (β := β i)) where
  castLE_hom h x := by simp [CastLE.castLE]

instance CastHom.instSumMap {ι : Type _} [PartialOrder ι] {α₁ β₁ α₂ β₂ : ι → Type _}
  [CastLE α₁] [CastLE β₁] [CastLE α₂] [CastLE β₂]
  {f₁ : ∀ i, α₁ i → α₂ i} {f₂ : ∀ i, β₁ i → β₂ i}
  [CastHom f₁] [CastHom f₂]
  : CastHom (f := fun i => Sum.map (f := f₁ i) (g := f₂ i)) where
  castLE_hom h x := by cases x <;> simp [CastLE.castLE, CastHom.castLE_hom]

instance EraseHom.instSumMap {ι : Type _} {α₁ β₁ α₂ β₂ : ι → Type _} {γ₁ γ₂ : Type _}
  [Erase α₁ γ₁] [Erase β₁ γ₂] [Erase α₂ γ₁] [Erase β₂ γ₂]
  {f₁ : ∀ i, α₁ i → α₂ i} {f₂ : ∀ i, β₁ i → β₂ i}
  [EraseHom γ₁ f₁] [EraseHom γ₂ f₂]
  : EraseHom (γ₁ ⊕ γ₂) (fun i => Sum.map (f := f₁ i) (g := f₂ i)) where
  erase_hom i x := by cases x <;> simp [erase, EraseHom.erase_hom]

instance CastHom.instSumElim {ι : Type _} [PartialOrder ι] {α β γ : ι → Type _}
  [CastLE α] [CastLE β] [CastLE γ]
  {f : ∀ i, α i → γ i} {g : ∀ i, β i → γ i}
  [CastHom f] [CastHom g]
  : CastHom (f := fun i => Sum.elim (f := f i) (g := g i)) where
  castLE_hom h x := by cases x <;> simp [CastLE.castLE, CastHom.castLE_hom]

--TODO: union behavior for erasure?
-- instance EraseHom.instSumElim {ι : Type _} {α β γ : ι → Type _} {δ : Type _}
--   [Erase α δ] [Erase β δ] [Erase γ δ]
--   {f : ∀ i, α i → γ i} {g : ∀ i, β i → γ i}
--   [EraseHom δ f] [EraseHom δ g]
--   : EraseHom δ (fun i => Sum.elim (f := f i) (g := g i)) where
--   erase_hom i x := by cases x <;> simp [erase, EraseHom.erase_hom]

class CastErase
  {ι : Type _} [PartialOrder ι] (α : ι → Type _) [CastLE α]
  (β : Type _) extends Erase α β where
  castHom_erase : CastHom erase
    := by simp only [Erase.erase]; infer_instance

class BindErase
  {ι : Type _} (α : ι → Type _) [∀ n, BinderList (α n)]
  (β : Type _) [BinderList β] extends Erase α β where
  binderHom_erase {i} (x : α i) : BinderListHom (erase i)
    := by simp only [Erase.erase]; infer_instance

attribute [instance] BindErase.binderHom_erase

class BindCastErase
  {ι : Type _} [PartialOrder ι] (α : ι → Type _) [∀ n, BinderList (α n)] [CastLE α]
  (β : Type _) [BinderList β] extends CastErase α β, BindErase α β where

end Gt3
