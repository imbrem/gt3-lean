import Gt3.Syntax.Tree.Defs.Node

namespace Gt3

open NumChildren BinderList HasChildren FlatChildren CastLE

inductive Node.SimRelUpto
  (stop : Prop) {α β} [BinderList α] [BinderList β] (rel : α → β → Prop) {ι₁ ι₂}
  (lhs : ι₁ → Node α ι₁ → Prop) (rhs : ι₂ → Node β ι₂ → Prop) : ℕ → ι₁ → ι₂ → Prop
  | done (i₁ i₂) : stop → SimRelUpto stop rel lhs rhs 0 i₁ i₂
  | node {i₁ i₂ n₁ n₂}
    (hn₁ : lhs i₁ n₁) (hn₂ : rhs i₂ n₂)
    (tag : rel n₁.tag n₂.tag)
    (numChildren : numChildren n₁.tag = numChildren n₂.tag)
    {gas}
    (children :
      ∀ j, SimRelUpto stop rel lhs rhs gas
            (getChild n₁ j) (getChild n₂ (j.cast numChildren)))
    : SimRelUpto stop rel lhs rhs (gas + 1) i₁ i₂

def Node.SimRel {α β} [BinderList α] [BinderList β] (rel : α → β → Prop) {ι₁ ι₂}
  (lhs : ι₁ → Node α ι₁ → Prop) (rhs : ι₂ → Node β ι₂ → Prop) (i₁ : ι₁) (i₂ : ι₂) : Prop
  := ∀n, Node.SimRelUpto ⊤ rel lhs rhs n i₁ i₂

def Node.FinSimRel {α β} [BinderList α] [BinderList β] (rel : α → β → Prop) {ι₁ ι₂}
  (lhs : ι₁ → Node α ι₁ → Prop) (rhs : ι₂ → Node β ι₂ → Prop) (i₁ : ι₁) (i₂ : ι₂) : Prop
  := ∃ n, Node.SimRelUpto ⊥ rel lhs rhs n i₁ i₂

def Node.Undef
  {α} [BinderList α] (rel : α → α → Prop) {ι}
  (addr : ι → Node α ι → Prop) (i : ι)
  : Prop
  := ¬ SimRel rel addr addr i i

def Node.Undef2
  {α} [BinderList α] (rel : α → α → Prop) {ι}
  (lhs : ι → Node α ι → Prop) (rhs : ι → Node α ι → Prop) (i₁ : ι) (i₂ : ι)
  : Prop
  := Undef rel lhs i₁ ∧ Undef rel rhs i₂

instance Node.Undef2.instSymm
  {α} [BinderList α] (rel : α → α → Prop) {ι}
  (addr : ι → Node α ι → Prop) : IsSymm ι (Node.Undef2 rel addr addr) where
  symm _ _ h := And.intro h.right h.left

instance Node.Undef2.instTrans
  {α} [BinderList α] (rel : α → α → Prop) {ι}
  (addr : ι → Node α ι → Prop) : IsTrans ι (Node.Undef2 rel addr addr) where
  trans _ _ _ h1 h2 := And.intro h1.left h2.right

class Determ {β} (e : β → β → Prop) {α} (r : α → β → Prop) where
  determ : ∀ {x y₁ y₂}, r x y₁ → r x y₂ → e y₁ y₂

theorem Determ.determ_eq {α β} {r : α → β → Prop}
  [Determ Eq r] {x y₁ y₂} (h₁ : r x y₁) (h₂ : r x y₂) : y₁ = y₂ :=
  determ h₁ h₂

class InhabAt {α} (P : α → Prop) {β} (r : α → β → Prop) where
  rel_inhab_at : ∀ x, P x → ∃ y, r x y

theorem InhabAt.rel_inhab {α β} (r : α → β → Prop)
  [InhabAt ⊤ r] (x) : ∃ y, r x y := InhabAt.rel_inhab_at (P := ⊤) x (by simp)

open Determ InhabAt

def readMem? {α β} (mem : α → Option β) (x : α) (y : β) : Prop := mem x = y

instance {α β} (mem : α → Option β) : Determ Eq (readMem? mem) where
  determ {x y₁ y₂} h₁ h₂ := by
    simp only [readMem?] at *
    generalize mem x = z at *
    cases z <;> cases h₁; cases h₂; rfl

def Node.SimUpto? (stop : Prop) {α β} [BinderList α] [BinderList β]
  (rel : α → β → Prop) {ι₁ ι₂}
  (lhs : ι₁ → Option (Node α ι₁)) (rhs : ι₂ → Option (Node β ι₂)) : ι₁ → ι₂ → ℕ → Prop
  := fun i₁ i₂ gas => Node.SimRelUpto stop rel (readMem? lhs) (readMem? rhs) gas i₁ i₂

def Node.Sim? {α β} [BinderList α] [BinderList β]
  (rel : α → β → Prop) {ι₁ ι₂}
  (lhs : ι₁ → Option (Node α ι₁)) (rhs : ι₂ → Option (Node β ι₂)) (i₁ : ι₁) (i₂ : ι₂) : Prop
  := Node.SimRel rel (readMem? lhs) (readMem? rhs) i₁ i₂

def readMem {α β} (mem : α → β) (x : α) (y : β) : Prop := mem x = y

instance {α β} (mem : α → β) : InhabAt ⊤ (readMem mem) where
  rel_inhab_at x _ := ⟨mem x, rfl⟩

instance {α β} (mem : α → β) : Determ Eq (readMem mem) where
  determ {x y₁ y₂} h₁ h₂ := by cases h₁; cases h₂; rfl

def Node.SimUpto (stop : Prop) {α β} [BinderList α] [BinderList β] (rel : α → β → Prop) {ι₁ ι₂}
  (lhs : ι₁ → Node α ι₁) (rhs : ι₂ → Node β ι₂) : ι₁ → ι₂ → Prop
  := fun i₁ i₂ => ∀ n, Node.SimRelUpto stop rel (readMem lhs) (readMem rhs) n i₁ i₂

def Node.Sim {α β} [BinderList α] [BinderList β] (rel : α → β → Prop) {ι₁ ι₂}
  (lhs : ι₁ → Node α ι₁) (rhs : ι₂ → Node β ι₂) (i₁ : ι₁) (i₂ : ι₂) : Prop
  := Node.SimRel rel (readMem lhs) (readMem rhs) i₁ i₂

def Node.FinSim {α β} [BinderList α] [BinderList β] (rel : α → β → Prop) {ι₁ ι₂}
  (lhs : ι₁ → Node α ι₁) (rhs : ι₂ → Node β ι₂) : ι₁ → ι₂ → Prop
  := fun i₁ i₂ => Node.FinSimRel rel (readMem lhs) (readMem rhs) i₁ i₂

section Sim

variable {stop : Prop} {α β} [BinderList α] [BinderList β]
        {data data₁ data₂ : α → β → Type _}
        {rel rel₁ rel₂ : α → β → Prop}
        {ι ι₁ ι₂}
        {addr : ι → Node α ι → Prop} {lhs : ι₁ → Node α ι₁ → Prop} {rhs : ι₂ → Node β ι₂ → Prop}
        {gas}
        {i : ι} {i₁ : ι₁} {i₂ : ι₂} {n₁ n₂}

namespace Node

theorem SimRelUpto.anti_gas
  {gas₁ gas₂} (h : gas₁ ≤ gas₂) {i₁ i₂}
  (h : SimRelUpto ⊤ rel lhs rhs gas₂ i₁ i₂) : SimRelUpto ⊤ rel lhs rhs gas₁ i₁ i₂
  := match h, gas₁ with
  | _, 0 => .done i₁ i₂ trivial
  | .node hn₁ hn₂ h_tag h_numChildren h_children, gas₁ + 1 =>
    .node hn₁ hn₂ h_tag h_numChildren
      (fun j => anti_gas (by convert h using 0; simp) (h_children j))

theorem SimRel.node
  (hn₁ : lhs i₁ n₁) (hn₂ : rhs i₂ n₂)
  (tag : rel n₁.tag n₂.tag)
  (numChildren : numChildren n₁.tag = numChildren n₂.tag)
  (children :
    ∀ j, SimRel rel lhs rhs
          (getChild n₁ j) (getChild n₂ (j.cast numChildren)))
  : SimRel rel lhs rhs i₁ i₂
  | 0 => .done i₁ i₂ trivial
  | n + 1 => .node hn₁ hn₂ tag numChildren (fun j => children j n)

-- theorem FinSimRel.sim {i₁ i₂}
--   : FinSimRel rel lhs rhs i₁ i₂ → SimRel rel lhs rhs i₁ i₂
--   | .node hn₁ hn₂ h_tag h_numChildren h_children =>
--     .node hn₁ hn₂ h_tag h_numChildren (fun j => FinSimRel.sim (h_children j))

-- theorem EFinTrace.fin_sim {i₁ i₂}
--   : EFinTrace data lhs rhs i₁ i₂ → FinSimRel (fun x y => Nonempty (data x y)) lhs rhs i₁ i₂
--   | .node hn₁ hn₂ h_tag h_numChildren h_children =>
--     .node hn₁ hn₂ ⟨h_tag⟩ h_numChildren (fun j => fin_sim (h_children j))

-- theorem EFinTrace.sim
--   : EFinTrace data lhs rhs i₁ i₂ → SimRel (fun x y => Nonempty (data x y)) lhs rhs i₁ i₂ :=
--   fun t => (t.fin_sim).sim

theorem SimRelUpto.notBot : SimRelUpto stop ⊥ lhs rhs (gas + 1) i₁ i₂ → False
  | .node _ _ h_tag _ _ => by cases h_tag

theorem SimRelUpto.ne_bot (h : SimRelUpto stop rel lhs rhs (gas + 1) i₁ i₂) : rel ≠ ⊥
  := fun e => (e ▸ h).notBot

theorem SimRel.notBot (h : SimRel ⊥ lhs rhs i₁ i₂) : False := (h 1).notBot

theorem SimRel.ne_bot (h : SimRel rel lhs rhs i₁ i₂) : rel ≠ ⊥ := (h 1).ne_bot

theorem FinSimRel.notBot : FinSimRel ⊥ lhs rhs i₁ i₂ → False
  := fun ⟨gas + 1, .node _ _ h_tag _ _⟩ => by cases h_tag

theorem FinSimRel.ne_bot (h : FinSimRel rel lhs rhs i₁ i₂) : rel ≠ ⊥
  := fun e => (e ▸ h).notBot

theorem SimRelUpto.mono_rel (hrel : rel₁ ≤ rel₂) {gas} {i₁ : ι₁} {i₂ : ι₂}
  : SimRelUpto stop rel₁ lhs rhs gas i₁ i₂ → SimRelUpto stop rel₂ lhs rhs gas i₁ i₂
  | .done _ _ hs => .done i₁ i₂ hs
  | .node hn₁ hn₂ h_tag h_numChildren h_children =>
    .node hn₁ hn₂ (hrel _ _ h_tag) h_numChildren (fun j => mono_rel hrel (h_children j))

theorem SimRel.mono_rel (hrel : rel₁ ≤ rel₂) {i₁ : ι₁} {i₂ : ι₂} (h : SimRel rel₁ lhs rhs i₁ i₂)
  : SimRel rel₂ lhs rhs i₁ i₂ := fun n => (h n).mono_rel hrel

theorem SimRelUpto.inf [Determ Eq lhs] [Determ Eq rhs] {gas} {i₁ : ι₁} {i₂ : ι₂}
  : SimRelUpto stop rel₁ lhs rhs gas i₁ i₂
  → SimRelUpto stop rel₂ lhs rhs gas i₁ i₂
  → SimRelUpto stop (rel₁ ⊓ rel₂) lhs rhs gas i₁ i₂
  | .done _ _ hs,
    .done _ _ _ => .done i₁ i₂ hs
  | .node hn₁ hn₂ h1_tag h1_numChildren h1_children,
    .node hn₁' hn₂' h2_tag _ h2_children => by
    cases determ_eq hn₁ hn₁'
    cases determ_eq hn₂ hn₂'
    exact .node (rel := rel₁ ⊓ rel₂)
      hn₁ hn₂
      (And.intro h1_tag h2_tag) h1_numChildren
      (fun j => SimRelUpto.inf (h1_children j) (h2_children j))

theorem SimRel.inf [Determ Eq lhs] [Determ Eq rhs] {i₁ : ι₁} {i₂ : ι₂}
  (h₁ : SimRel rel₁ lhs rhs i₁ i₂)
  (h₂ : SimRel rel₂ lhs rhs i₁ i₂) : SimRel (rel₁ ⊓ rel₂) lhs rhs i₁ i₂ :=
  fun n => SimRelUpto.inf (h₁ n) (h₂ n)

theorem SimRelUpto.lhs_of_inf
  : SimRelUpto stop (rel₁ ⊓ rel₂) lhs rhs gas i₁ i₂ → SimRelUpto stop rel₁ lhs rhs gas i₁ i₂
  := mono_rel (by simp)

theorem SimRelUpto.rhs_of_inf
  : SimRelUpto stop (rel₁ ⊓ rel₂) lhs rhs gas i₁ i₂ → SimRelUpto stop rel₂ lhs rhs gas i₁ i₂
  := mono_rel (by simp)

theorem SimRelUpto.inf_iff [Determ Eq lhs] [Determ Eq rhs]
  : SimRelUpto stop (rel₁ ⊓ rel₂) lhs rhs gas i₁ i₂
    ↔ SimRelUpto stop rel₁ lhs rhs gas i₁ i₂ ∧ SimRelUpto stop rel₂ lhs rhs gas i₁ i₂ :=
  ⟨fun h => ⟨lhs_of_inf h, rhs_of_inf h⟩,
   fun ⟨h1, h2⟩ => inf h1 h2⟩

theorem SimRel.lhs_of_inf
  : SimRel (rel₁ ⊓ rel₂) lhs rhs i₁ i₂ → SimRel rel₁ lhs rhs i₁ i₂ := mono_rel (by simp)

theorem SimRel.rhs_of_inf
  : SimRel (rel₁ ⊓ rel₂) lhs rhs i₁ i₂ → SimRel rel₂ lhs rhs i₁ i₂ := mono_rel (by simp)

theorem SimRel.inf_iff [Determ Eq lhs] [Determ Eq rhs]
  : SimRel (rel₁ ⊓ rel₂) lhs rhs i₁ i₂
    ↔ SimRel rel₁ lhs rhs i₁ i₂ ∧ SimRel rel₂ lhs rhs i₁ i₂ :=
  ⟨fun h => ⟨lhs_of_inf h, rhs_of_inf h⟩,
   fun ⟨h1, h2⟩ => inf h1 h2⟩

-- TODO: need inhabitance...
theorem SimRelUpto.refl
  {rel} [IsRefl α rel]
  {addr : ι → Node α ι → Prop} [InhabAt ⊤ addr]
  {gas} (i) : SimRelUpto ⊤ rel addr addr gas i i
  := match gas with
  | 0 => .done i i trivial
  | _ + 1 =>
    have ⟨y, hy⟩ := rel_inhab addr i;
    .node hy hy (IsRefl.refl _) rfl (fun j => refl (getChild y j))

theorem SimRel.refl
  {rel} [IsRefl α rel] {addr : ι → Node α ι → Prop} [InhabAt ⊤ addr] (i) : SimRel rel addr addr i i
  := fun _ => .refl i

theorem SimRelUpto.symm {rel} [IsSymm α rel]
  {lhs : ι₁ → Node α ι₁ → Prop} {rhs : ι₂ → Node α ι₂ → Prop}
  {gas} {i₁ i₂}
  : SimRelUpto stop rel lhs rhs gas i₁ i₂ → SimRelUpto stop rel rhs lhs gas i₂ i₁
  | .done _ _ hs => .done i₂ i₁ hs
  | .node hn₁ hn₂ h_tag h_numChildren h_children =>
    .node hn₂ hn₁ (IsSymm.symm _ _ h_tag) h_numChildren.symm
      (fun j => symm (h_children (j.cast (Eq.symm h_numChildren))))

theorem SimRel.symm {rel} [IsSymm α rel]
  {lhs : ι₁ → Node α ι₁ → Prop} {rhs : ι₂ → Node α ι₂ → Prop}
  {i₁ i₂}
  (h : SimRel rel lhs rhs i₁ i₂) : SimRel rel rhs lhs i₂ i₁
  := fun n => (h n).symm

theorem SimRelUpto.gtrans
  {α β γ} [BinderList α] [BinderList β] [BinderList γ]
  {rel₁ : α → β → Prop} {rel₂ : β → γ → Prop} {rel₃ : α → γ → Prop}
  (hrel : ∀ a b c, rel₁ a b → rel₂ b c → rel₃ a c)
  {ι₁ ι₂ ι₃}
  {lhs : ι₁ → Node α ι₁ → Prop} {mid : ι₂ → Node β ι₂ → Prop} {rhs : ι₃ → Node γ ι₃ → Prop}
  [Determ Eq lhs] [Determ Eq mid] [Determ Eq rhs]
  {gas} {i₁ i₂ i₃}
  : SimRelUpto stop rel₁ lhs mid gas i₁ i₂ → SimRelUpto stop rel₂ mid rhs gas i₂ i₃
    → SimRelUpto stop rel₃ lhs rhs gas i₁ i₃
  | .done _ _ hs, .done _ _ _ => .done i₁ i₃ hs
  | .node hn₁ hn₂ h1_tag h1_numChildren h1_children,
    .node hn₂' hn₃ h2_tag h2_numChildren h2_children => by
    cases determ_eq hn₂ hn₂'
    exact .node hn₁ hn₃ (hrel _ _ _ h1_tag h2_tag) (h1_numChildren.trans h2_numChildren)
      (fun j => gtrans hrel (h1_children j) (h2_children (j.cast h1_numChildren)))

theorem SimRel.gtrans
  {α β γ} [BinderList α] [BinderList β] [BinderList γ]
  {rel₁ : α → β → Prop} {rel₂ : β → γ → Prop} {rel₃ : α → γ → Prop}
  (hrel : ∀ a b c, rel₁ a b → rel₂ b c → rel₃ a c)
  {ι₁ ι₂ ι₃}
  {lhs : ι₁ → Node α ι₁ → Prop} {mid : ι₂ → Node β ι₂ → Prop} {rhs : ι₃ → Node γ ι₃ → Prop}
  [Determ Eq lhs] [Determ Eq mid] [Determ Eq rhs]
  {i₁ i₂ i₃}
  (h1 : SimRel rel₁ lhs mid i₁ i₂)
  (h2 : SimRel rel₂ mid rhs i₂ i₃)
  : SimRel rel₃ lhs rhs i₁ i₃
  := fun n => SimRelUpto.gtrans hrel (h1 n) (h2 n)

theorem SimRelUpto.trans {rel} [IsTrans α rel]
  {ι₁ ι₂ ι₃}
  {lhs : ι₁ → Node α ι₁ → Prop} {mid : ι₂ → Node α ι₂ → Prop} {rhs : ι₃ → Node α ι₃ → Prop}
  [Determ Eq lhs] [Determ Eq mid] [Determ Eq rhs]
  {gas} {i₁ i₂ i₃}
  (h1 : SimRelUpto stop rel lhs mid gas i₁ i₃)
  (h2 : SimRelUpto stop rel mid rhs gas i₃ i₂)
  : SimRelUpto stop rel lhs rhs gas i₁ i₂
  := h1.gtrans IsTrans.trans h2

theorem SimRel.trans {rel} [IsTrans α rel]
  {ι₁ ι₂ ι₃}
  {lhs : ι₁ → Node α ι₁ → Prop} {mid : ι₂ → Node α ι₂ → Prop} {rhs : ι₃ → Node α ι₃ → Prop}
  [Determ Eq lhs] [Determ Eq mid] [Determ Eq rhs]
  {i₁ i₂ i₃}
  (h1 : SimRel rel lhs mid i₁ i₃)
  (h2 : SimRel rel mid rhs i₃ i₂)
  : SimRel rel lhs rhs i₁ i₂
  := h1.gtrans IsTrans.trans h2

end Node

end Sim

/-- A pre-cotree over a given address space -/
structure PCotree (ι : Type _) (α : Type _) [NumChildren α] : Type _ where
  ix : ι
  getNode : ι → Node α ι

def PCotree.Sim {ι₁ ι₂ α β} [BinderList α] [BinderList β] (rel : α → β → Prop)
  (t₁ : PCotree ι₁ α) (t₂ : PCotree ι₂ β) : Prop
  := Node.Sim rel t₁.getNode t₂.getNode t₁.ix t₂.ix

theorem PCotree.Sim.refl {ι α} [BinderList α]
  {rel} [IsRefl α rel]
  (t : PCotree ι α) : PCotree.Sim rel t t :=
  Node.SimRel.refl t.ix

theorem PCotree.Sim.symm {ι₁ ι₂ α} [BinderList α]
  {rel} [IsSymm α rel]
  {t₁ : PCotree ι₁ α} {t₂ : PCotree ι₂ α}
  (h : PCotree.Sim rel t₁ t₂) : PCotree.Sim rel t₂ t₁ :=
  Node.SimRel.symm h

theorem PCotree.Sim.trans {ι₁ ι₂ ι₃ α} [BinderList α]
  {rel} [IsTrans α rel]
  {t₁ : PCotree ι₁ α} {t₂ : PCotree ι₂ α} {t₃ : PCotree ι₃ α}
  (h1 : PCotree.Sim rel t₁ t₂)
  (h2 : PCotree.Sim rel t₂ t₃) : PCotree.Sim rel t₁ t₃ :=
  Node.SimRel.trans h1 h2

instance PCotree.setoid (ι α) [BinderList α] : Setoid (PCotree ι α) where
  r := PCotree.Sim Eq
  iseqv := ⟨Sim.refl, Sim.symm, Sim.trans⟩

def Cotree (ι : Type _) (α : Type _) [BinderList α] : Type _ := Quotient (PCotree.setoid ι α)

def PCotree.toCotree {ι α} [BinderList α] (t : PCotree ι α) : Cotree ι α := ⟦t⟧

/-- A pre-cotree over a given partial address space -/
structure PCotree? (ι : Type _) (α : Type _) [NumChildren α] : Type _ where
  ix : ι
  getNode : ι → Option (Node α ι)

def PCotree?.Sim? {ι₁ ι₂ α β} [BinderList α] [BinderList β] (rel : α → β → Prop)
  (t₁ : PCotree? ι₁ α) (t₂ : PCotree? ι₂ β) : Prop
  := Node.Sim? rel t₁.getNode t₂.getNode t₁.ix t₂.ix

theorem PCotree?.Sim?.symm {ι₁ ι₂ α} [BinderList α]
  {rel} [IsSymm α rel]
  {t₁ : PCotree? ι₁ α} {t₂ : PCotree? ι₂ α}
  (h : PCotree?.Sim? rel t₁ t₂) : PCotree?.Sim? rel t₂ t₁ :=
  Node.SimRel.symm h

theorem PCotree?.Sim?.trans {ι₁ ι₂ ι₃ α} [BinderList α]
  {rel} [IsTrans α rel]
  {t₁ : PCotree? ι₁ α} {t₂ : PCotree? ι₂ α} {t₃ : PCotree? ι₃ α}
  (h1 : PCotree?.Sim? rel t₁ t₂)
  (h2 : PCotree?.Sim? rel t₂ t₃) : PCotree?.Sim? rel t₁ t₃ :=
  Node.SimRel.trans h1 h2

theorem PCotree?.Sim?.lhs {ι₁ ι₂ α} [BinderList α]
  {rel} [IsSymm α rel] [IsTrans α rel]
  {t₁ : PCotree? ι₁ α} {t₂ : PCotree? ι₂ α}
  (h : PCotree?.Sim? rel t₁ t₂) : PCotree?.Sim? rel t₁ t₁ :=
  h.trans h.symm

theorem PCotree?.Sim?.rhs {ι₁ ι₂ α} [BinderList α]
  {rel} [IsSymm α rel] [IsTrans α rel]
  {t₁ : PCotree? ι₁ α} {t₂ : PCotree? ι₂ α}
  (h : PCotree?.Sim? rel t₁ t₂) : PCotree?.Sim? rel t₂ t₂ :=
  h.symm.lhs

def PCotree?.Undef {ι α} [BinderList α]
  (rel : α → α → Prop)
  (t : PCotree? ι α) : Prop
  := ¬ PCotree?.Sim? rel t t

theorem PCotree?.Undef.not_lhs {ι₁ ι₂ α} [BinderList α]
  {rel : α → α → Prop} [IsSymm α rel] [IsTrans α rel]
  {t₁ : PCotree? ι₁ α} {t₂ : PCotree? ι₂ α}
  (h : PCotree?.Undef rel t₁) : ¬ PCotree?.Sim? rel t₁ t₂ :=
  fun hsim => h hsim.lhs

theorem PCotree?.Undef.not_rhs {ι₁ ι₂ α} [BinderList α]
  {rel : α → α → Prop} [IsSymm α rel] [IsTrans α rel]
  {t₁ : PCotree? ι₁ α} {t₂ : PCotree? ι₂ α}
  (h : PCotree?.Undef rel t₂) : ¬ PCotree?.Sim? rel t₁ t₂ :=
  fun hsim => h hsim.rhs

def PCotree?.Sim {ι₁ ι₂ α} [BinderList α] (rel : α → α → Prop)
  (t₁ : PCotree? ι₁ α) (t₂ : PCotree? ι₂ α) : Prop
  := t₁.Sim? rel t₂ ∨ (t₁.Undef rel ∧ t₂.Undef rel)

theorem PCotree?.Sim.refl {ι α} [BinderList α]
  {rel} [IsRefl α rel]
  (t : PCotree? ι α) : PCotree?.Sim rel t t :=
  open Classical in
  if h : t.Sim? rel t then
    Or.inl h
  else
    Or.inr ⟨h, h⟩

theorem PCotree?.Sim.symm {ι₁ ι₂ α} [BinderList α]
  {rel} [IsSymm α rel]
  {t₁ : PCotree? ι₁ α} {t₂ : PCotree? ι₂ α}
  (h : PCotree?.Sim rel t₁ t₂) : PCotree?.Sim rel t₂ t₁ :=
  match h with
  | Or.inl hsim => Or.inl (PCotree?.Sim?.symm hsim)
  | Or.inr ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩

theorem PCotree?.Sim.trans {ι₁ ι₂ ι₃ α} [BinderList α]
  {rel} [IsSymm α rel] [IsTrans α rel]
  {t₁ : PCotree? ι₁ α} {t₂ : PCotree? ι₂ α} {t₃ : PCotree? ι₃ α}
  (h1 : PCotree?.Sim rel t₁ t₂)
  (h2 : PCotree?.Sim rel t₂ t₃) : PCotree?.Sim rel t₁ t₃ :=
  match h1, h2 with
  | Or.inl hsim1, Or.inl hsim2 => Or.inl (PCotree?.Sim?.trans hsim1 hsim2)
  | Or.inl hsim1, Or.inr ⟨h2_undef1, _⟩ => (h2_undef1.not_rhs hsim1).elim
  | Or.inr ⟨_, h1_undef2⟩, Or.inl hsim2 => (h1_undef2.not_lhs hsim2).elim
  | Or.inr ⟨h1_undef1, _⟩, Or.inr ⟨_, h2_undef2⟩ =>
    Or.inr ⟨h1_undef1, h2_undef2⟩

instance PCotree?.setoid (ι α) [BinderList α] : Setoid (PCotree? ι α) where
  r := PCotree?.Sim Eq
  iseqv := ⟨Sim.refl, Sim.symm, Sim.trans⟩

def Cotree? (ι : Type _) (α : Type _) [BinderList α] : Type _
  := Quotient (PCotree?.setoid ι α)

/-- A pre-cotree over a finite address space -/
structure PFCotree (α : Type _) [NumChildren α] where
  size : ℕ
  cotree : PCotree (Fin size) α

def PFCotree.Sim {α β} [BinderList α] [BinderList β] (rel : α → β → Prop)
  (t₁ : PFCotree α) (t₂ : PFCotree β) : Prop
  := t₁.cotree.Sim rel t₂.cotree

theorem PFCotree.Sim.refl {α} [BinderList α]
  {rel} [IsRefl α rel]
  (t : PFCotree α) : PFCotree.Sim rel t t :=
  PCotree.Sim.refl t.cotree

theorem PFCotree.Sim.symm {α} [BinderList α]
  {rel} [IsSymm α rel]
  {t₁ : PFCotree α} {t₂ : PFCotree α}
  (h : PFCotree.Sim rel t₁ t₂) : PFCotree.Sim rel t₂ t₁ :=
  PCotree.Sim.symm h

theorem PFCotree.Sim.trans {α} [BinderList α]
  {rel} [IsTrans α rel]
  {t₁ : PFCotree α} {t₂ : PFCotree α} {t₃ : PFCotree α}
  (h1 : PFCotree.Sim rel t₁ t₂)
  (h2 : PFCotree.Sim rel t₂ t₃) : PFCotree.Sim rel t₁ t₃ :=
  PCotree.Sim.trans h1 h2

instance PFCotree.setoid (α) [BinderList α] : Setoid (PFCotree α) where
  r := PFCotree.Sim Eq
  iseqv := ⟨Sim.refl, Sim.symm, Sim.trans⟩

def FCotree (α : Type _) [BinderList α] : Type _ := Quotient (PFCotree.setoid α)

/-- A pre-cotree over a finite partial address space -/
structure PFCotree? (α : Type _) [NumChildren α] where
  size : ℕ
  cotree : PCotree? (Fin size) α

def PFCotree?.Sim? {α β} [BinderList α] [BinderList β] (rel : α → β → Prop)
  (t₁ : PFCotree? α) (t₂ : PFCotree? β) : Prop
  := t₁.cotree.Sim? rel t₂.cotree

theorem PFCotree?.Sim?.symm {α} [BinderList α]
  {rel} [IsSymm α rel]
  {t₁ : PFCotree? α} {t₂ : PFCotree? α}
  (h : PFCotree?.Sim? rel t₁ t₂) : PFCotree?.Sim? rel t₂ t₁ :=
  PCotree?.Sim?.symm h

theorem PFCotree?.Sim?.trans {α} [BinderList α]
  {rel} [IsTrans α rel]
  {t₁ : PFCotree? α} {t₂ : PFCotree? α} {t₃ : PFCotree? α}
  (h1 : PFCotree?.Sim? rel t₁ t₂)
  (h2 : PFCotree?.Sim? rel t₂ t₃) : PFCotree?.Sim? rel t₁ t₃ :=
  PCotree?.Sim?.trans h1 h2

def PFCotree?.Sim {α} [BinderList α] (rel : α → α → Prop)
  (t₁ : PFCotree? α) (t₂ : PFCotree? α) : Prop
  := t₁.cotree.Sim rel t₂.cotree

theorem PFCotree?.Sim.refl {α} [BinderList α]
  {rel} [IsRefl α rel]
  (t : PFCotree? α) : PFCotree?.Sim rel t t :=
  PCotree?.Sim.refl t.cotree

theorem PFCotree?.Sim.symm {α} [BinderList α]
  {rel} [IsSymm α rel]
  {t₁ : PFCotree? α} {t₂ : PFCotree? α}
  (h : PFCotree?.Sim rel t₁ t₂) : PFCotree?.Sim rel t₂ t₁ :=
  PCotree?.Sim.symm h

theorem PFCotree?.Sim.trans {α} [BinderList α]
  {rel} [IsSymm α rel] [IsTrans α rel]
  {t₁ : PFCotree? α} {t₂ : PFCotree? α} {t₃ : PFCotree? α}
  (h1 : PFCotree?.Sim rel t₁ t₂)
  (h2 : PFCotree?.Sim rel t₂ t₃) : PFCotree?.Sim rel t₁ t₃ :=
  PCotree?.Sim.trans h1 h2

instance PFCotree?.setoid (α) [BinderList α] : Setoid (PFCotree? α) where
  r := PFCotree?.Sim Eq
  iseqv := ⟨Sim.refl, Sim.symm, Sim.trans⟩

def FCotree? (α : Type _) [BinderList α] : Type _ := Quotient (PFCotree?.setoid α)

end Gt3
