import Mathlib.Data.Finset.Defs
import Mathlib.Data.SetLike.Basic

import Gt3.Tree.Node

namespace Gt3

class AddrVals (μ : Type _) (ι : Type _) (α : outParam (Type _)) where
  getVals : μ → ι → Set α

class AddrVals.ExistsOut (μ : Type _) {ι α}
  (setIn : Set ι) (setOut : Set α) [AddrVals μ ι α] where
  map_mem : ∀ {m : μ}, ∀ i ∈ setIn, ∃ v ∈ getVals m i, v ∈ setOut

class AddrVals.ForallOut (μ : Type _) {ι α}
  (setIn : Set ι) (setOut : Set α) [AddrVals μ ι α] where
  map_mem : ∀ {m : μ}, ∀ i ∈ setIn, ∀ v ∈ getVals m i, v ∈ setOut

class AddrVals.Out (μ : Type _) {ι α}
  (relIn : ι → ι → Prop) (relOut : α → α → Prop) [AddrVals μ ι α]
  where
  map_rel : ∀ {m : μ}, ∀ {i₁ i₂}, relIn i₁ i₂ →
    ∀ v₁ ∈ getVals m i₁, ∀ v₂ ∈ getVals m i₂, relOut v₁ v₂

class AddrVals.In (μ : Type _) {ι α}
  (relIn : ι → ι → Prop) (relOut : α → α → Prop) [AddrVals μ ι α]
  where
  reflect_rel : ∀ {m : μ} {i₁ i₂},
    ∀ v₁ ∈ getVals m i₁, ∀ v₂ ∈ getVals m i₂, relOut v₁ v₂ → relIn i₁ i₂

abbrev AddrVals.ExistsWith (μ : Type _) ι {α} (setOut : Set α) [AddrVals μ ι α]
  := ExistsOut μ (Set.univ : Set ι) setOut

abbrev AddrVals.Inhab (μ ι α) [AddrVals μ ι α]
  := ExistsWith μ ι (Set.univ : Set α)

theorem AddrVals.ExistsWith.inhab
  {μ ι α} [vals : AddrVals μ ι α]
  (setOut : Set α) [hinhab : ExistsWith μ ι setOut] (m : μ) (i : ι)
  : (getVals (α := α) m i).Nonempty :=
  let ⟨v, hv⟩ := AddrVals.ExistsOut.map_mem (setOut := setOut) (m := m) (i := i) (Set.mem_univ i)
  ⟨v, hv.1⟩

theorem AddrVals.Inhab.inhab
  {μ ι α} [vals : AddrVals μ ι α] [hinhab : Inhab μ ι α] (m : μ) (i : ι)
  : (getVals (α := α) m i).Nonempty :=
  AddrVals.ExistsWith.inhab (setOut := Set.univ) m i

abbrev AddrVals.PartIn? (μ) {ι} (relIn : ι → ι → Prop) (α) [AddrVals μ ι α]
  := AddrVals.Out μ relIn (Eq (α := α))

abbrev AddrVals.Det (μ ι α) [AddrVals μ ι α]
  := AddrVals.PartIn? μ (Eq (α := ι)) α

theorem AddrVals.Det.det
  {μ ι α} [vals : AddrVals μ ι α] [det : AddrVals.Det μ ι α]
  {m : μ} {i : ι}
  : ∀ v₁ ∈ getVals m i, ∀ v₂ ∈ getVals m i, v₁ = v₂ :=
  Out.map_rel rfl

theorem AddrVals.Det.mk
  {μ ι α} [vals : AddrVals μ ι α]
  (hdet : ∀ {m : μ} {i : ι}, ∀ v₁ ∈ getVals m i, ∀ v₂ ∈ getVals m i, v₁ = v₂)
  : AddrVals.Det μ ι α where
  map_rel h := by cases h; exact hdet

class AddrVal? (μ : Type _) (ι : Type _) (α : Type _) extends AddrVals μ ι α where
  getVal? : μ → ι → Option α
  mem_getVals_iff_some : ∀ (m : μ) (i v), v ∈ getVals m i ↔ getVal? m i = some v

instance AddrVal?.instDet (μ ι α) [av : AddrVal? μ ι α] : AddrVals.Det μ ι α
  := AddrVals.Det.mk
    (fun _ h _ h' => by rw [mem_getVals_iff_some] at *; rw [h] at h'; cases h'; rfl)

class AddrVal (μ : Type _) (ι : Type _) (α : Type _) extends AddrVal? μ ι α where
  getVal : μ → ι → α
  mem_getVals_iff_eq : ∀ (m : μ) (i v), v ∈ getVals m i ↔ getVal m i = v

@[simp]
theorem AddrVal.getVals?_eq
  {μ ι α} [av : AddrVal μ ι α] (m : μ) (i : ι)
  : av.getVal? m i = some (av.getVal m i) :=
  by rw [<-AddrVal?.mem_getVals_iff_some, AddrVal.mem_getVals_iff_eq]

attribute [simp] AddrVal.mem_getVals_iff_eq AddrVal?.mem_getVals_iff_some

instance AddrVal.instInhab (μ ι α) [av : AddrVal μ ι α] : AddrVals.Inhab μ ι α where
  map_mem := by simp [mem_getVals_iff_eq]

instance AddrVals.instMapSet {ι α} : AddrVals (ι → Set α) ι α where
  getVals m := m

instance AddrVals.instMapFinset.{u} {ι : Type u} {α : Type u} : AddrVals (ι → Finset α) ι α where
  getVals m i := m i

instance AddrVal?.instMapOption {ι α} : AddrVal? (ι → Option α) ι α where
  getVals m i v := m i = some v
  getVal? m := m
  mem_getVals_iff_some _ _ _ := Iff.rfl

instance AddrVal.instMap {ι α} : AddrVal (ι → α) ι α where
  getVals m i v := m i = v
  getVal? m i := some (m i)
  getVal m := m
  mem_getVals_iff_some _ _ _ := by simp only [Option.some.injEq]; rfl
  mem_getVals_iff_eq _ _ _ := Iff.rfl

end Gt3
