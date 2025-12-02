import Gt3.Syntax.Tree.Defs.Node

namespace Gt3

open NumChildren BinderList HasChildren FlatChildren CastLE

inductive Node.SimUpto {α β} [BinderList α] [BinderList β] (rel : α → β → Prop) {ι₁ ι₂}
  (lhs : ι₁ → Node α ι₁) (rhs : ι₂ → Node β ι₂) : ℕ → ι₁ → ι₂ → Prop
  | done (i₁ i₂) : SimUpto rel lhs rhs 0 i₁ i₂
  | node {i₁ i₂}
    (tag : rel (lhs i₁).tag (rhs i₂).tag)
    (numChildren : numChildren (lhs i₁).tag = numChildren (rhs i₂).tag)
    {gas}
    (children :
      ∀ j, SimUpto rel lhs rhs gas
            (getChild (lhs i₁) j) (getChild (rhs i₂) (j.cast numChildren)))
    : SimUpto rel lhs rhs (gas + 1) i₁ i₂

def Node.Sim {α β} [BinderList α] [BinderList β] (rel : α → β → Prop) {ι₁ ι₂}
  (lhs : ι₁ → Node α ι₁) (rhs : ι₂ → Node β ι₂) (i₁ : ι₁) (i₂ : ι₂) : Prop
  := ∀n, Node.SimUpto rel lhs rhs n i₁ i₂

inductive Node.FinSim {α β} [BinderList α] [BinderList β] (rel : α → β → Prop) {ι₁ ι₂}
  (lhs : ι₁ → Node α ι₁) (rhs : ι₂ → Node β ι₂) : ι₁ → ι₂ → Prop
  | node {i₁ i₂}
    (tag : rel (lhs i₁).tag (rhs i₂).tag)
    (numChildren : numChildren (lhs i₁).tag = numChildren (rhs i₂).tag)
    (children :
      ∀ j, FinSim rel lhs rhs
            (getChild (lhs i₁) j) (getChild (rhs i₂) (j.cast numChildren)))
    : FinSim rel lhs rhs i₁ i₂

inductive Node.FinTrace {α β} [BinderList α] [BinderList β] (data : α → β → Type _) {ι₁ ι₂}
  (lhs : ι₁ → Node α ι₁) (rhs : ι₂ → Node β ι₂) : ι₁ → ι₂ → Type _
  | node {i₁ i₂}
    (tag : data (lhs i₁).tag (rhs i₂).tag)
    (numChildren : numChildren (lhs i₁).tag = numChildren (rhs i₂).tag)
    (children :
      ∀ j, FinTrace data lhs rhs
            (getChild (lhs i₁) j) (getChild (rhs i₂) (j.cast numChildren)))
    : FinTrace data lhs rhs i₁ i₂

section Sim

variable {α β} [BinderList α] [BinderList β]
        {data data₁ data₂ : α → β → Type _}
        {rel rel₁ rel₂ : α → β → Prop}
        {ι ι₁ ι₂} {addr : ι → Node α ι} {lhs : ι₁ → Node α ι₁} {rhs : ι₂ → Node β ι₂}
        {gas}
        {i : ι} {i₁ : ι₁} {i₂ : ι₂}

namespace Node

theorem SimUpto.anti_gas
  {gas₁ gas₂} (h : gas₁ ≤ gas₂) {i₁ i₂}
  (h : SimUpto rel lhs rhs gas₂ i₁ i₂) : SimUpto rel lhs rhs gas₁ i₁ i₂
  := match h, gas₁ with
  | _, 0 => .done i₁ i₂
  | .node h_tag h_numChildren h_children, gas₁ + 1 =>
    .node h_tag h_numChildren (fun j => anti_gas (by convert h using 0; simp) (h_children j))

theorem Sim.node
  (tag : rel (lhs i₁).tag (rhs i₂).tag)
  (numChildren : numChildren (lhs i₁).tag = numChildren (rhs i₂).tag)
  (children :
    ∀ j, Sim rel lhs rhs
          (getChild (lhs i₁) j) (getChild (rhs i₂) (j.cast numChildren)))
  : Sim rel lhs rhs i₁ i₂
  | 0 => .done i₁ i₂
  | n + 1 => .node tag numChildren (fun j => children j n)

theorem SimUpto.tag {gas} {i₁ i₂}
  (h : SimUpto rel lhs rhs (gas + 1) i₁ i₂) : rel (lhs i₁).tag (rhs i₂).tag
  := match h with | .node h_tag _ _ => h_tag

theorem SimUpto.numChildren_eq {gas} {i₁ i₂}
  : SimUpto rel lhs rhs (gas + 1) i₁ i₂ → numChildren (lhs i₁).tag = numChildren (rhs i₂).tag
  | .node _ h_numChildren _ => h_numChildren

theorem SimUpto.children {gas} {i₁ i₂}
  (h : SimUpto rel lhs rhs (gas + 1) i₁ i₂) (j : Fin (numChildren (lhs i₁).tag))
  : SimUpto rel lhs rhs gas (getChild (lhs i₁) j) (getChild (rhs i₂) (j.cast h.numChildren_eq))
  := match h with | .node _ _ h_children => h_children j

theorem Sim.tag (h : Sim rel lhs rhs i₁ i₂)
  : rel (lhs i₁).tag (rhs i₂).tag :=
  (h 1).tag

theorem Sim.numChildren_eq (h : Sim rel lhs rhs i₁ i₂)
  : numChildren (lhs i₁).tag = numChildren (rhs i₂).tag :=
  (h 1).numChildren_eq

theorem Sim.children (h : Sim rel lhs rhs i₁ i₂) (j : Fin (numChildren (lhs i₁).tag))
  : Sim rel lhs rhs (getChild (lhs i₁) j) (getChild (rhs i₂) (j.cast h.numChildren_eq)) :=
  fun n => (h (n + 1)).children j

theorem Sim.node_iff
  : Sim rel lhs rhs i₁ i₂
    ↔ rel (lhs i₁).tag (rhs i₂).tag ∧
      ∃ h : numChildren (lhs i₁).tag = numChildren (rhs i₂).tag ,
        (∀ j, Sim rel lhs rhs
            (getChild (lhs i₁) j) (getChild (rhs i₂) (j.cast h)))
  := ⟨
    fun h => ⟨h.tag, ⟨h.numChildren_eq, h.children⟩⟩,
    fun ⟨h_tag, ⟨h_numChildren, h_children⟩⟩ => .node h_tag h_numChildren h_children
  ⟩

theorem FinSim.sim {i₁ i₂}
  : FinSim rel lhs rhs i₁ i₂ → Sim rel lhs rhs i₁ i₂
  | .node h_tag h_numChildren h_children =>
    .node h_tag h_numChildren (fun j => FinSim.sim (h_children j))

theorem FinTrace.fin_sim {i₁ i₂}
  : FinTrace data lhs rhs i₁ i₂ → FinSim (fun x y => Nonempty (data x y)) lhs rhs i₁ i₂
  | .node h_tag h_numChildren h_children =>
    .node ⟨h_tag⟩ h_numChildren (fun j => fin_sim (h_children j))

theorem FinTrace.sim
  : FinTrace data lhs rhs i₁ i₂ → Sim (fun x y => Nonempty (data x y)) lhs rhs i₁ i₂ :=
  fun t => (t.fin_sim).sim

theorem SimUpto.notBot : SimUpto ⊥ lhs rhs (gas + 1) i₁ i₂ → False
  | .node h_tag _ _ => by cases h_tag

theorem SimUpto.ne_bot (h : SimUpto rel lhs rhs (gas + 1) i₁ i₂) : rel ≠ ⊥
  := fun e => (e ▸ h).notBot

theorem Sim.notBot (h : Sim ⊥ lhs rhs i₁ i₂) : False := (h 1).notBot

theorem Sim.ne_bot (h : Sim rel lhs rhs i₁ i₂) : rel ≠ ⊥ := (h 1).ne_bot

theorem FinSim.notBot : FinSim ⊥ lhs rhs i₁ i₂ → False
  | .node h_tag _ _ => by cases h_tag

theorem FinSim.ne_bot (h : FinSim rel lhs rhs i₁ i₂) : rel ≠ ⊥
  := fun e => (e ▸ h).notBot

theorem SimUpto.mono (hrel : rel₁ ≤ rel₂) {gas} {i₁ : ι₁} {i₂ : ι₂}
  : SimUpto rel₁ lhs rhs gas i₁ i₂ → SimUpto rel₂ lhs rhs gas i₁ i₂
  | .done _ _ => .done i₁ i₂
  | .node h_tag h_numChildren h_children =>
    .node (hrel _ _ h_tag) h_numChildren (fun j => mono hrel (h_children j))

theorem Sim.mono (hrel : rel₁ ≤ rel₂) {i₁ : ι₁} {i₂ : ι₂} (h : Sim rel₁ lhs rhs i₁ i₂)
  : Sim rel₂ lhs rhs i₁ i₂ := fun n => (h n).mono hrel

theorem FinSim.mono (hrel : rel₁ ≤ rel₂) {i₁ : ι₁} {i₂ : ι₂}
  : FinSim rel₁ lhs rhs i₁ i₂ → FinSim rel₂ lhs rhs i₁ i₂
  | .node h_tag h_numChildren h_children =>
    .node (hrel _ _ h_tag) h_numChildren (fun j => mono hrel (h_children j))

def FinTrace.map (f : ∀ tag₁ tag₂, data₁ tag₁ tag₂ → data₂ tag₁ tag₂)
  {i₁ : ι₁} {i₂ : ι₂}
  : FinTrace data₁ lhs rhs i₁ i₂ → FinTrace data₂ lhs rhs i₁ i₂
  | .node h_tag h_numChildren h_children =>
    .node (f _ _ h_tag) h_numChildren (fun j => map f (h_children j))

theorem SimUpto.inf {gas} {i₁ : ι₁} {i₂ : ι₂}
  : SimUpto rel₁ lhs rhs gas i₁ i₂
  → SimUpto rel₂ lhs rhs gas i₁ i₂
  → SimUpto (rel₁ ⊓ rel₂) lhs rhs gas i₁ i₂
  | .done _ _,
    .done _ _ => .done i₁ i₂
  | .node h1_tag h1_numChildren h1_children,
    .node h2_tag _ h2_children =>
    .node (rel := rel₁ ⊓ rel₂) (And.intro h1_tag h2_tag) h1_numChildren
      (fun j => SimUpto.inf (h1_children j) (h2_children j))

theorem Sim.inf {i₁ : ι₁} {i₂ : ι₂}
  (h₁ : Sim rel₁ lhs rhs i₁ i₂)
  (h₂ : Sim rel₂ lhs rhs i₁ i₂) : Sim (rel₁ ⊓ rel₂) lhs rhs i₁ i₂ :=
  fun n => SimUpto.inf (h₁ n) (h₂ n)

theorem FinSim.inf {i₁ : ι₁} {i₂ : ι₂}
  : FinSim rel₁ lhs rhs i₁ i₂
  → FinSim rel₂ lhs rhs i₁ i₂
  → FinSim (rel₁ ⊓ rel₂) lhs rhs i₁ i₂
  | .node h1_tag h1_numChildren h1_children,
    .node h2_tag _ h2_children =>
    .node
      (And.intro h1_tag h2_tag)
      h1_numChildren
      (fun j => FinSim.inf (h1_children j) (h2_children j))

def FinTrace.prod {i₁ : ι₁} {i₂ : ι₂}
  : FinTrace data₁ lhs rhs i₁ i₂
  → FinTrace data₂ lhs rhs i₁ i₂
  → FinTrace (fun x y => data₁ x y × data₂ x y) lhs rhs i₁ i₂
  | .node h1_tag h1_numChildren h1_children,
    .node h2_tag _ h2_children =>
    .node
      (h1_tag, h2_tag)
      h1_numChildren
      (fun j => FinTrace.prod (h1_children j) (h2_children j))

theorem SimUpto.lhs_of_inf
  : SimUpto (rel₁ ⊓ rel₂) lhs rhs gas i₁ i₂ → SimUpto rel₁ lhs rhs gas i₁ i₂
  := mono (by simp)

theorem SimUpto.rhs_of_inf
  : SimUpto (rel₁ ⊓ rel₂) lhs rhs gas i₁ i₂ → SimUpto rel₂ lhs rhs gas i₁ i₂
  := mono (by simp)

theorem SimUpto.inf_iff
  : SimUpto (rel₁ ⊓ rel₂) lhs rhs gas i₁ i₂
    ↔ SimUpto rel₁ lhs rhs gas i₁ i₂ ∧ SimUpto rel₂ lhs rhs gas i₁ i₂ :=
  ⟨fun h => ⟨lhs_of_inf h, rhs_of_inf h⟩,
   fun ⟨h1, h2⟩ => inf h1 h2⟩

theorem Sim.lhs_of_inf
  : Sim (rel₁ ⊓ rel₂) lhs rhs i₁ i₂ → Sim rel₁ lhs rhs i₁ i₂ := mono (by simp)

theorem Sim.rhs_of_inf
  : Sim (rel₁ ⊓ rel₂) lhs rhs i₁ i₂ → Sim rel₂ lhs rhs i₁ i₂ := mono (by simp)

theorem Sim.inf_iff
  : Sim (rel₁ ⊓ rel₂) lhs rhs i₁ i₂
    ↔ Sim rel₁ lhs rhs i₁ i₂ ∧ Sim rel₂ lhs rhs i₁ i₂ :=
  ⟨fun h => ⟨lhs_of_inf h, rhs_of_inf h⟩,
   fun ⟨h1, h2⟩ => inf h1 h2⟩

theorem FinSim.lhs_of_inf
  : FinSim (rel₁ ⊓ rel₂) lhs rhs i₁ i₂ → FinSim rel₁ lhs rhs i₁ i₂ := mono (by simp)

theorem FinSim.rhs_of_inf
  : FinSim (rel₁ ⊓ rel₂) lhs rhs i₁ i₂ → FinSim rel₂ lhs rhs i₁ i₂ := mono (by simp)

theorem FinSim.inf_iff
  : FinSim (rel₁ ⊓ rel₂) lhs rhs i₁ i₂
    ↔ FinSim rel₁ lhs rhs i₁ i₂ ∧ FinSim rel₂ lhs rhs i₁ i₂ :=
  ⟨fun h => ⟨lhs_of_inf h, rhs_of_inf h⟩,
   fun ⟨h1, h2⟩ => inf h1 h2⟩

theorem FinSim.sup_of_lhs
  : FinSim rel₁ lhs rhs i₁ i₂ → FinSim (rel₁ ⊔ rel₂) lhs rhs i₁ i₂ := mono (by simp)

theorem FinSim.sup_of_rhs
  : FinSim rel₂ lhs rhs i₁ i₂ → FinSim (rel₁ ⊔ rel₂) lhs rhs i₁ i₂ := mono (by simp)

theorem SimUpto.refl
  {rel} [IsRefl α rel] {addr : ι → Node α ι} {gas} (i) : SimUpto rel addr addr gas i i
  := match gas with
  | 0 => .done i i
  | _ + 1 => .node (IsRefl.refl _) rfl (fun j => refl (getChild (addr i) j))

theorem Sim.refl
  {rel} [IsRefl α rel] {addr : ι → Node α ι} (i) : Sim rel addr addr i i
  := fun _ => .refl i

theorem SimUpto.symm {rel} [IsSymm α rel]
  {lhs : ι₁ → Node α ι₁} {rhs : ι₂ → Node α ι₂}
  {gas} {i₁ i₂}
  : SimUpto rel lhs rhs gas i₁ i₂ → SimUpto rel rhs lhs gas i₂ i₁
  | .done _ _ => .done i₂ i₁
  | .node h_tag h_numChildren h_children =>
    .node (IsSymm.symm _ _ h_tag) h_numChildren.symm
      (fun j => symm (h_children (j.cast (Eq.symm h_numChildren))))

theorem Sim.symm {rel} [IsSymm α rel]
  {lhs : ι₁ → Node α ι₁} {rhs : ι₂ → Node α ι₂}
  {i₁ i₂}
  (h : Sim rel lhs rhs i₁ i₂) : Sim rel rhs lhs i₂ i₁
  := fun n => (h n).symm

theorem FinSim.symm {rel} [IsSymm α rel]
  {lhs : ι₁ → Node α ι₁} {rhs : ι₂ → Node α ι₂}
  {i₁ i₂}
  : FinSim rel lhs rhs i₁ i₂ → FinSim rel rhs lhs i₂ i₁
  | .node h_tag h_numChildren h_children =>
    .node (IsSymm.symm _ _ h_tag) h_numChildren.symm
      (fun j => symm (h_children (j.cast (Eq.symm h_numChildren))))

theorem SimUpto.gtrans
  {α β γ} [BinderList α] [BinderList β] [BinderList γ]
  {rel₁ : α → β → Prop}
  {rel₂ : β → γ → Prop}
  {rel₃ : α → γ → Prop}
  (hrel : ∀ a b c, rel₁ a b → rel₂ b c → rel₃ a c)
  {ι₁ ι₂ ι₃} {lhs : ι₁ → Node α ι₁} {mid : ι₂ → Node β ι₂} {rhs : ι₃ → Node γ ι₃}
  {gas} {i₁ i₂ i₃}
  : SimUpto rel₁ lhs mid gas i₁ i₂ → SimUpto rel₂ mid rhs gas i₂ i₃ → SimUpto rel₃ lhs rhs gas i₁ i₃
  | .done _ _, .done _ _ => .done i₁ i₃
  | .node h1_tag h1_numChildren h1_children,
    .node h2_tag h2_numChildren h2_children =>
    .node (hrel _ _ _ h1_tag h2_tag) (h1_numChildren.trans h2_numChildren)
      (fun j => gtrans hrel (h1_children j) (h2_children (j.cast h1_numChildren)))

theorem Sim.gtrans
  {α β γ} [BinderList α] [BinderList β] [BinderList γ]
  {rel₁ : α → β → Prop}
  {rel₂ : β → γ → Prop}
  {rel₃ : α → γ → Prop}
  (hrel : ∀ a b c, rel₁ a b → rel₂ b c → rel₃ a c)
  {ι₁ ι₂ ι₃} {lhs : ι₁ → Node α ι₁} {mid : ι₂ → Node β ι₂} {rhs : ι₃ → Node γ ι₃}
  {i₁ i₂ i₃}
  (h1 : Sim rel₁ lhs mid i₁ i₂)
  (h2 : Sim rel₂ mid rhs i₂ i₃)
  : Sim rel₃ lhs rhs i₁ i₃
  := fun n => SimUpto.gtrans hrel (h1 n) (h2 n)

theorem SimUpto.trans {rel} [IsTrans α rel]
  {ι₁ ι₂ ι₃} {lhs : ι₁ → Node α ι₁} {rhs : ι₂ → Node α ι₂} {mid : ι₃ → Node α ι₃}
  {gas} {i₁ i₂ i₃}
  (h1 : SimUpto rel lhs mid gas i₁ i₃)
  (h2 : SimUpto rel mid rhs gas i₃ i₂)
  : SimUpto rel lhs rhs gas i₁ i₂
  := h1.gtrans IsTrans.trans h2

theorem Sim.trans {rel} [IsTrans α rel]
  {ι₁ ι₂ ι₃} {lhs : ι₁ → Node α ι₁} {rhs : ι₂ → Node α ι₂} {mid : ι₃ → Node α ι₃}
  {i₁ i₂ i₃}
  (h1 : Sim rel lhs mid i₁ i₃)
  (h2 : Sim rel mid rhs i₃ i₂)
  : Sim rel lhs rhs i₁ i₂
  := h1.gtrans IsTrans.trans h2

--TODO: FinSim.{trans, gtrans}

end Node

end Sim

/-- A pre-cotree over a given address space -/
structure PCotree (ι : Type _) (α : Type _) [NumChildren α] : Type _ where
  ix : ι
  getNode : ι → Node α ι

def PCotree.Sim {ι₁ ι₂ α β} [BinderList α] [BinderList β] (rel : α → β → Prop)
  (t₁ : PCotree ι₁ α) (t₂ : PCotree ι₂ β) : Prop
  := Node.Sim rel t₁.getNode t₂.getNode t₁.ix t₂.ix

/-- A finite cotree over a given address space -/
structure PFCotree (α : Type _) [NumChildren α] where
  size : ℕ
  cotree : PCotree (Fin size) α

def PFCotree.Sim {α β} [BinderList α] [BinderList β] (rel : α → β → Prop)
  (t₁ : PFCotree α) (t₂ : PFCotree β) : Prop
  := t₁.cotree.Sim rel t₂.cotree

/-- A graph with the given tag type and index type -/
structure Graph (ι : Type _) (α : Type _) [NumChildren α] (ℓ : Type _) : Type _ where
  output : ℓ → ι
  getNode : ι → Node α ι

abbrev Graph.outputNode {ι α} [NumChildren α] {ℓ}
  (g : Graph ι α ℓ) (l : ℓ) : Node α ι := g.getNode (g.output l)

/-- A simulation of two graphs -/
def Graph.Sim {ι₁ ι₂ α β} [BinderList α] [BinderList β] (rel : α → β → Prop) {ℓ}
  (g₁ : Graph ι₁ α ℓ) (g₂ : Graph ι₂ β ℓ) : Prop
  := ∀ l, Node.Sim rel g₁.getNode g₂.getNode (g₁.output l) (g₂.output l)

/-- A finite graph with a given tag type and index type -/
structure FinGraph (α : Type _) [NumChildren α] (ℓ : Type _) : Type _ where
  size : ℕ
  graph : Graph (Fin size) α ℓ

abbrev FinGraph.output {α : Type _} [NumChildren α] {ℓ : Type _}
  (g : FinGraph α ℓ) : ℓ → Fin g.size := g.graph.output

abbrev FinGraph.getNode {α : Type _} [NumChildren α] {ℓ : Type _}
  (g : FinGraph α ℓ) : Fin g.size → Node α (Fin g.size) := g.graph.getNode

/-- A simulation of two finite graphs -/
def FinGraph.Sim {α β} [BinderList α] [BinderList β] (rel : α → β → Prop) {ℓ}
  (g₁ : FinGraph α ℓ) (g₂ : FinGraph β ℓ) : Prop
  := g₁.graph.Sim rel g₂.graph

end Gt3
