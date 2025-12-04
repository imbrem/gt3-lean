import Gt3.Tree.Basic
import Gt3.Memory.Basic

namespace Gt3

open NumChildren BinderList HasChildren GetTag FlatChildren AddrVals

variable
  {μ₁ μ₂ μ₃ ι₁ ι₂ ι₃ α₁ α₂ α₃}
  [BinderList α₁] [BinderList α₂] [BinderList α₃]

section MultiAddr

variable
  [AddrVals μ₁ ι₁ (Node α₁ ι₁)] [AddrVals μ₂ ι₂ (Node α₂ ι₂)] [AddrVals μ₃ ι₃ (Node α₃ ι₃)]

inductive SimIxRelUpto
  (stop : Prop) (rel : α₁ → α₂ → Prop) (lhs : μ₁) (rhs : μ₂) : ℕ → ι₁ → ι₂ → Prop
  | done (i₁ i₂) : stop → SimIxRelUpto stop rel lhs rhs 0 i₁ i₂
  | node {i₁ i₂ t₁ t₂}
    (hn₁ : t₁ ∈ getVals lhs i₁) (hn₂ : t₂ ∈ getVals rhs i₂)
    (tag : rel t₁.tag t₂.tag)
    (numChildren : numChildren t₁ = numChildren t₂)
    {gas}
    (children :
      ∀ j, SimIxRelUpto stop rel lhs rhs gas
            (getChild t₁ j) (getChild t₂ (j.cast numChildren)))
    : SimIxRelUpto stop rel lhs rhs (gas + 1) i₁ i₂

def SimIxRel (rel : α₁ → α₂ → Prop) (lhs : μ₁) (rhs : μ₂) (i₁ : ι₁) (i₂ : ι₂) : Prop
  := ∀n, SimIxRelUpto ⊤ rel lhs rhs n i₁ i₂

inductive TreeSimIxRel
  (rel : α₁ → α₂ → Prop) (lhs : μ₁) (rhs : μ₂) : ι₁ → ι₂ → Prop
  | node {i₁ i₂ t₁ t₂}
    (hn₁ : t₁ ∈ getVals lhs i₁) (hn₂ : t₂ ∈ getVals rhs i₂)
    (tag : rel t₁.tag t₂.tag)
    (numChildren : numChildren t₁ = numChildren t₂)
    (children :
      ∀ j, TreeSimIxRel rel lhs rhs
            (getChild t₁ j) (getChild t₂ (j.cast numChildren)))
    : TreeSimIxRel rel lhs rhs i₁ i₂

variable
  {stop gas} {rel rel₁ rel₂ : α₁ → α₂ → Prop} {lhs : μ₁} {rhs : μ₂} {i₁ : ι₁} {i₂ : ι₂} {n₁ n₂}

theorem SimIxRelUpto.anti_gas
  {gas₁ gas₂} (h : gas₁ ≤ gas₂) {i₁ : ι₁} {i₂ : ι₂}
  (h : SimIxRelUpto ⊤ rel lhs rhs gas₂ i₁ i₂) : SimIxRelUpto ⊤ rel lhs rhs gas₁ i₁ i₂
  := match h, gas₁ with
  | _, 0 => .done i₁ i₂ trivial
  | .node hn₁ hn₂ h_tag h_numChildren h_children, gas₁ + 1 =>
    .node hn₁ hn₂ h_tag h_numChildren
      (fun j => anti_gas (by convert h using 0; simp) (h_children j))

theorem SimIxRel.node
  (hn₁ : n₁ ∈ getVals lhs i₁) (hn₂ : n₂ ∈ getVals rhs i₂)
  (tag : rel n₁.tag n₂.tag)
  (numChildren : numChildren n₁.tag = numChildren n₂.tag)
  (children :
    ∀ j, SimIxRel (ι₁ := ι₁) (ι₂ := ι₂) rel lhs rhs
          (getChild n₁ j) (getChild n₂ (j.cast numChildren)))
  : SimIxRel rel lhs rhs i₁ i₂
  | 0 => .done i₁ i₂ trivial
  | n + 1 => .node hn₁ hn₂ tag numChildren (fun j => children j n)

theorem SimIxRelUpto.notBot : SimIxRelUpto stop ⊥ lhs rhs (gas + 1) i₁ i₂ → False
  | .node _ _ h_tag _ _ => by cases h_tag

theorem SimIxRelUpto.ne_bot (h : SimIxRelUpto stop rel lhs rhs (gas + 1) i₁ i₂) : rel ≠ ⊥
  := fun e => (e ▸ h).notBot

theorem SimIxRel.notBot (h : SimIxRel ⊥ lhs rhs i₁ i₂) : False := (h 1).notBot

theorem SimIxRel.ne_bot (h : SimIxRel rel lhs rhs i₁ i₂) : rel ≠ ⊥ := (h 1).ne_bot

theorem SimIxRelUpto.mono_rel (hrel : rel₁ ≤ rel₂) {gas} {i₁ : ι₁} {i₂ : ι₂}
  : SimIxRelUpto stop rel₁ lhs rhs gas i₁ i₂ → SimIxRelUpto stop rel₂ lhs rhs gas i₁ i₂
  | .done _ _ hs => .done i₁ i₂ hs
  | .node hn₁ hn₂ h_tag h_numChildren h_children =>
    .node hn₁ hn₂ (hrel _ _ h_tag) h_numChildren (fun j => mono_rel hrel (h_children j))

theorem SimIxRel.mono_rel (hrel : rel₁ ≤ rel₂) {i₁ : ι₁} {i₂ : ι₂} (h : SimIxRel rel₁ lhs rhs i₁ i₂)
  : SimIxRel rel₂ lhs rhs i₁ i₂ := fun n => (h n).mono_rel hrel

section GTrans

variable
  {rel₁ : α₁ → α₂ → Prop} {rel₂ : α₂ → α₃ → Prop} {rel₃ : α₁ → α₃ → Prop}
  {lhs : μ₁} {mid : μ₂} {rhs : μ₃}

theorem SimIxRelUpto.gtrans
  [AddrVals.Det μ₁ ι₁ (Node α₁ ι₁)]
  [AddrVals.Det μ₂ ι₂ (Node α₂ ι₂)]
  [AddrVals.Det μ₃ ι₃ (Node α₃ ι₃)]
  (hrel : ∀ a b c, rel₁ a b → rel₂ b c → rel₃ a c)
  {gas} {i₁ : ι₁} {i₂ : ι₂} {i₃ : ι₃}
  : SimIxRelUpto stop rel₁ lhs mid gas i₁ i₂ → SimIxRelUpto stop rel₂ mid rhs gas i₂ i₃
    → SimIxRelUpto stop rel₃ lhs rhs gas i₁ i₃
  | .done _ _ hs, .done _ _ _ => .done i₁ i₃ hs
  | .node hn₁ hn₂ h1_tag h1_numChildren h1_children,
    .node hn₂' hn₃ h2_tag h2_numChildren h2_children => by
    cases AddrVals.Det.det _ hn₂ _ hn₂'
    exact .node hn₁ hn₃ (hrel _ _ _ h1_tag h2_tag) (h1_numChildren.trans h2_numChildren)
      (fun j => gtrans hrel (h1_children j) (h2_children (j.cast h1_numChildren)))

theorem SimIxRel.gtrans
  [AddrVals.Det μ₁ ι₁ (Node α₁ ι₁)]
  [AddrVals.Det μ₂ ι₂ (Node α₂ ι₂)]
  [AddrVals.Det μ₃ ι₃ (Node α₃ ι₃)]
  (hrel : ∀ a b c, rel₁ a b → rel₂ b c → rel₃ a c)
  {i₁ : ι₁} {i₂ : ι₂} {i₃ : ι₃}
  (h1 : SimIxRel rel₁ lhs mid i₁ i₂)
  (h2 : SimIxRel rel₂ mid rhs i₂ i₃)
  : SimIxRel rel₃ lhs rhs i₁ i₃
  := fun n => SimIxRelUpto.gtrans hrel (h1 n) (h2 n)

end GTrans

end MultiAddr

section SingleAddr

variable
  {α μ ι}
  [BinderList α]
  [AddrVals μ ι (Node α ι)]
  [AddrVals μ₁ ι₁ (Node α ι₁)] [AddrVals μ₂ ι₂ (Node α ι₂)] [AddrVals μ₃ ι₃ (Node α ι₃)]
  {stop gas}
  {rel : α → α → Prop}
  {addr : μ} {lhs : μ₁} {rhs : μ₂}

theorem SimIxRelUpto.refl
  [IsRefl α rel] [AddrVals.Inhab μ ι (Node α ι)]
  {gas} (i : ι) : SimIxRelUpto ⊤ rel addr addr gas i i
  := match gas with
  | 0 => .done i i trivial
  | _ + 1 =>
    have ⟨y, hy⟩ := AddrVals.Inhab.inhab addr i;
    .node hy hy (IsRefl.refl _) rfl (fun j => refl (getChild y j))

theorem SimIxRel.refl
  [IsRefl α rel] [AddrVals.Inhab μ ι (Node α ι)] (i : ι) : SimIxRel rel addr addr i i
  := fun _ => .refl i

theorem SimIxRelUpto.symm [IsSymm α rel]
  {gas} {i₁ : ι₁} {i₂ : ι₂}
  : SimIxRelUpto stop rel lhs rhs gas i₁ i₂ → SimIxRelUpto stop rel rhs lhs gas i₂ i₁
  | .done _ _ hs => .done i₂ i₁ hs
  | .node hn₁ hn₂ h_tag h_numChildren h_children =>
    .node hn₂ hn₁ (IsSymm.symm _ _ h_tag) h_numChildren.symm
      (fun j => symm (h_children (j.cast (Eq.symm h_numChildren))))

theorem SimIxRel.symm {rel} [IsSymm α rel]
  {i₁ : ι₁} {i₂ : ι₂} (h : SimIxRel rel lhs rhs i₁ i₂) : SimIxRel rel rhs lhs i₂ i₁
  := fun n => (h n).symm

variable
  {lhs : μ₁} {mid : μ₂} {rhs : μ₃}

theorem SimIxRelUpto.trans {rel} [IsTrans α rel]
  [AddrVals.Det μ₁ ι₁ (Node α ι₁)]
  [AddrVals.Det μ₂ ι₂ (Node α ι₂)]
  [AddrVals.Det μ₃ ι₃ (Node α ι₃)]
  {gas} {i₁ : ι₁} {i₂ : ι₂} {i₃ : ι₃}
  (h1 : SimIxRelUpto stop rel lhs mid gas i₁ i₂)
  (h2 : SimIxRelUpto stop rel mid rhs gas i₂ i₃)
  : SimIxRelUpto stop rel lhs rhs gas i₁ i₃
  := h1.gtrans IsTrans.trans h2

theorem SimIxRel.trans {rel} [IsTrans α rel]
  [AddrVals.Det μ₁ ι₁ (Node α ι₁)]
  [AddrVals.Det μ₂ ι₂ (Node α ι₂)]
  [AddrVals.Det μ₃ ι₃ (Node α ι₃)] {i₁ : ι₁} {i₂ : ι₂} {i₃ : ι₃}
  (h1 : SimIxRel rel lhs mid i₁ i₂)
  (h2 : SimIxRel rel mid rhs i₂ i₃)
  : SimIxRel rel lhs rhs i₁ i₃
  := h1.gtrans IsTrans.trans h2

end SingleAddr

end Gt3
