import Gt3.Tree.Node
import Gt3.Cotree.SimIx

namespace Gt3

open NumChildren BinderList HasChildren FlatChildren

-- section Sim

-- variable {stop : Prop} {α β} [BinderList α] [BinderList β]
--         {data data₁ data₂ : α → β → Type _}
--         {rel rel₁ : α → β → Prop}
--         {ι₁ ι₂ ι₁' ι₂'}
--         {lhs : ι₁ → Node α ι₁} {rhs : ι₂ → Node β ι₂}
--         {i₁ : ι₁} {i₂ : ι₂} {n₁ n₂}

-- -- TODO: map things using injections

-- -- TODO: such mappings give us ≈ objects...

-- -- TODO: letting us play ℕ games to build cotrees out of trees!

-- namespace Node

-- theorem SimUpto.map_lhs {gas}
--   {i₁ i₂} (f : ι₁ → ι₁') (g : ι₁' → ι₁)
--   (hfg : ∀ i, g (f i) = i)
--   : SimUpto stop rel lhs rhs gas i₁ i₂
--   → SimUpto stop rel (Node.mapChildren f ∘ lhs ∘ g) rhs gas (f i₁) i₂
--   | .done _ _ hs => .done (f i₁) i₂ hs
--   | .node (n₁ := n₁) hn₁ hn₂ h_tag h_numChildren h_children =>
--     .node (lhs := readMem (Node.mapChildren f ∘ lhs ∘ g))
--           (rhs := readMem rhs)
--           (n₁ := n₁.mapChildren f)
--           (by simp only [hfg, implies_true, readMem, Function.comp_apply] at *; rw [hn₁]) hn₂
--           (by simp [mapChildren, h_tag]) (by simp [mapChildren, h_numChildren])
--           (fun j => map_lhs f g hfg (h_children j))

-- theorem SimUpto.map_rhs {gas}
--   {i₁ i₂} (f : ι₂ → ι₂') (g : ι₂' → ι₂)
--   (hfg : ∀ i, g (f i) = i)
--   : SimUpto stop rel lhs rhs gas i₁ i₂
--   → SimUpto stop rel lhs (Node.mapChildren f ∘ rhs ∘ g) gas i₁ (f i₂)
--   | .done _ _ hs => .done i₁ (f i₂) hs
--   | .node (n₂ := n₂) hn₁ hn₂ h_tag h_numChildren h_children =>
--     .node (lhs := readMem lhs)
--           (rhs := readMem (Node.mapChildren f ∘ rhs ∘ g))
--           (n₂ := n₂.mapChildren f)
--           hn₁
--           (by simp only [hfg, implies_true, readMem, Function.comp_apply] at *; rw [hn₂])
--           (by simp [mapChildren, h_tag]) (by simp [mapChildren, h_numChildren])
--           (fun j => map_rhs f g hfg (h_children j))

-- theorem SimUpto.map_both
--   {gas} {ι ι'} (f : ι → ι') (g : ι' → ι)
--   (hfg : ∀ i, g (f i) = i)
--   {lhs : ι → Node α ι}
--   {rhs : ι → Node β ι}
--   {i₁ i₂}
--   : SimUpto stop rel lhs rhs gas i₁ i₂
--   → SimUpto stop rel
--      (Node.mapChildren f ∘ lhs ∘ g) (Node.mapChildren f ∘ rhs ∘ g) gas (f i₁) (f i₂)
--   := fun h => (h.map_lhs f g hfg).map_rhs f g hfg

-- theorem Sim.map_lhs
--   {ι₁'} (f : ι₁ → ι₁') (g : ι₁' → ι₁)
--   (hfg : ∀ i, g (f i) = i)
--   {i₁ i₂}
--   : Sim rel lhs rhs i₁ i₂
--   → Sim rel (Node.mapChildren f ∘ lhs ∘ g) rhs (f i₁) i₂
--   := fun h n => SimUpto.map_lhs f g hfg (h n)

-- theorem Sim.map_rhs
--   {ι₂'} (f : ι₂ → ι₂') (g : ι₂' → ι₂)
--   (hfg : ∀ i, g (f i) = i)
--   {i₁ i₂}
--   : Sim rel lhs rhs i₁ i₂
--   → Sim rel lhs (Node.mapChildren f ∘ rhs ∘ g) i₁ (f i₂)
--   := fun h n => SimUpto.map_rhs f g hfg (h n)

-- theorem Sim.map_both
--   {ι ι'} (f : ι → ι') (g : ι' → ι)
--   (hfg : ∀ i, g (f i) = i)
--   {lhs : ι → Node α ι} {rhs : ι → Node β ι}
--   {i₁ i₂}
--   : Sim rel lhs rhs i₁ i₂
--   → Sim rel (Node.mapChildren f ∘ lhs ∘ g) (Node.mapChildren f ∘ rhs ∘ g) (f i₁) (f i₂)
--   := fun h n => SimUpto.map_both f g hfg (h n)

-- end Node

-- end Sim

/-- A pre-cotree over a given address space -/
structure PCotree (ι : Type _) (α : Type _) [NumChildren α] : Type _ where
  ix : ι
  getNode : ι → Node α ι

def PCotree.root {ι α} [NumChildren α] (t : PCotree ι α) : Node α ι := t.getNode t.ix

def PCotree.tag {ι α} [NumChildren α] (t : PCotree ι α) : α := t.root.tag

instance PCotree.instBinderList {ι α} [BinderList α] : BinderList (PCotree ι α) where
  numChildren t := numChildren t.tag
  binderList t := binderList t.tag
  getBinder t := getBinder t.tag
  getBinder_eq t := getBinder_eq t.tag

instance PCotree.instFlatChildrenIx {ι α} [BinderList α]
  : FlatChildren (PCotree ι α) ι where
  getDChild t j := getChild (t.getNode t.ix) j

instance PCotree.instFlatChildren {ι α} [BinderList α]
  : FlatChildren (PCotree ι α) (PCotree ι α) where
  getDChild t j := { ix := getChild t j, getNode := t.getNode }

def PCotree.Sim {ι₁ ι₂ α β} [BinderList α] [BinderList β] (rel : α → β → Prop)
  (t₁ : PCotree ι₁ α) (t₂ : PCotree ι₂ β) : Prop
  := SimIx rel t₁.getNode t₂.getNode t₁.ix t₂.ix

theorem PCotree.Sim.refl {ι α} [BinderList α]
  {rel} [IsRefl α rel]
  (t : PCotree ι α) : PCotree.Sim rel t t :=
  SimIx.refl t.ix

theorem PCotree.Sim.symm {ι₁ ι₂ α} [BinderList α]
  {rel} [IsSymm α rel]
  {t₁ : PCotree ι₁ α} {t₂ : PCotree ι₂ α}
  (h : PCotree.Sim rel t₁ t₂) : PCotree.Sim rel t₂ t₁ :=
  SimIx.symm h

theorem PCotree.Sim.trans {ι₁ ι₂ ι₃ α} [BinderList α]
  {rel} [IsTrans α rel]
  {t₁ : PCotree ι₁ α} {t₂ : PCotree ι₂ α} {t₃ : PCotree ι₃ α}
  (h1 : PCotree.Sim rel t₁ t₂)
  (h2 : PCotree.Sim rel t₂ t₃) : PCotree.Sim rel t₁ t₃ :=
  SimIx.trans h1 h2

theorem PCotree.Sim.tag {ι₁ ι₂ α β} [BinderList α] [BinderList β]
  {rel} {t₁ : PCotree ι₁ α} {t₂ : PCotree ι₂ β}
  (h : PCotree.Sim rel t₁ t₂) : rel t₁.tag t₂.tag :=
  let hsim := h 1
  match hsim with
  | .node hn₁ hn₂ h_tag _ _ => by
    cases hn₁; cases hn₂;
    exact h_tag

theorem PCotree.Sim.numChildren {ι₁ ι₂ α β} [BinderList α] [BinderList β]
  {rel} {t₁ : PCotree ι₁ α} {t₂ : PCotree ι₂ β}
  (h : PCotree.Sim rel t₁ t₂) : numChildren t₁ = numChildren t₂ :=
  let hsim := h 1
  match hsim with
  | .node hn₁ hn₂ h_tag h_numChildren _ => by
    cases hn₁; cases hn₂;
    exact h_numChildren

theorem PCotree.Sim.childrenIx {ι₁ ι₂ α β} [BinderList α] [BinderList β]
  {rel} {t₁ : PCotree ι₁ α} {t₂ : PCotree ι₂ β}
  (h : PCotree.Sim rel t₁ t₂) (j) :
  SimIx rel t₁.getNode t₂.getNode
    (getChild (β := ι₁) t₁ j) (getChild (β := ι₂) t₂ (j.cast (PCotree.Sim.numChildren h)))
  := fun n =>
    let hsim := h (n + 1)
    match hsim with
    | .node hn₁ hn₂ h_tag h_numChildren h_children => by
      cases hn₁; cases hn₂;
      exact h_children j

theorem PCotree.Sim.children {ι₁ ι₂ α β} [BinderList α] [BinderList β]
  {rel} {t₁ : PCotree ι₁ α} {t₂ : PCotree ι₂ β}
  (h : PCotree.Sim rel t₁ t₂) (j) :
  PCotree.Sim rel
    (getChild (β := PCotree ι₁ α) t₁ j)
    (getChild (β := PCotree ι₂ β) t₂ (j.cast (PCotree.Sim.numChildren h)))
  := fun n =>
    let hsim := h (n + 1)
    match hsim with
    | .node hn₁ hn₂ h_tag h_numChildren h_children => by
      cases hn₁; cases hn₂
      exact h_children j

instance PCotree.setoid (ι α) [BinderList α] : Setoid (PCotree ι α) where
  r := PCotree.Sim Eq
  iseqv := ⟨Sim.refl, Sim.symm, Sim.trans⟩

theorem PCotree.eqv_tag {ι α} [BinderList α]
  {t₁ t₂ : PCotree ι α} (h : t₁ ≈ t₂) : t₁.tag = t₂.tag := Sim.tag h

theorem PCotree.eqv_numChildren {ι α} [BinderList α]
  {t₁ t₂ : PCotree ι α} (h : t₁ ≈ t₂) : numChildren t₁ = numChildren t₂ := Sim.numChildren h

theorem PCotree.eqv_childrenIx {ι α} [BinderList α]
  {t₁ t₂ : PCotree ι α} (h : t₁ ≈ t₂) (j) :
  SimIx Eq t₁.getNode t₂.getNode
    (getChild (β := ι) t₁ j) (getChild (β := ι) t₂ (j.cast (PCotree.eqv_numChildren h)))
  := Sim.childrenIx h j

theorem PCotree.eqv_children {ι α} [BinderList α]
  {t₁ t₂ : PCotree ι α} (h : t₁ ≈ t₂) (j)
  : (getChild (β := PCotree ι α) t₁ j) ≈ (getChild t₂ (j.cast (PCotree.eqv_numChildren h)))
  := Sim.children h j

theorem PCotree.neZero {n} {α} [NumChildren α]
  (t : PCotree (Fin n) α) : NeZero n :=
  by cases n with
     | zero => exact t.ix.elim0
     | succ _ => infer_instance

def PCotree.mapIx {ι₁ ι₂ α} [NumChildren α]
  (f : ι₁ → ι₂) (g : ι₂ → ι₁)
  (t : PCotree ι₁ α) : PCotree ι₂ α where
  ix := f t.ix
  getNode i := (t.getNode (g i)).mapChildren f

-- theorem PCotree.mapIx_sim_eq {ι₁ ι₂ α} [BinderList α]
--   (f : ι₁ → ι₂) (g : ι₂ → ι₁)
--   (hfg : ∀ i, g (f i) = i)
--   (t : PCotree ι₁ α) :
--   t.Sim Eq (t.mapIx f g) := by
--   exact Node.Sim.map_rhs f g hfg (Sim.refl t)

-- theorem PCotree.mapIx_eqv {ι₁ ι₂ α} [BinderList α]
--   {f : ι₁ → ι₂} {g : ι₂ → ι₁}
--   (hfg : ∀ i, g (f i) = i)
--   {t t' : PCotree ι₁ α} (h : t ≈ t') :
--   (t.mapIx f g) ≈ (t'.mapIx f g)
--   := ((t.mapIx_sim_eq f g hfg).symm.trans h).trans (t'.mapIx_sim_eq f g hfg)

def PCotree.finToNat {n} {α} [NumChildren α] (t : PCotree (Fin n) α) : PCotree ℕ α
  := t.mapIx Fin.val (have _ := t.neZero; Fin.ofNat n)

-- theorem PCotree.finToNat_sim_eq {n} {α} [BinderList α] (t : PCotree (Fin n) α) :
--   t.Sim Eq t.finToNat
--   :=
--   have _  := t.neZero;
--   PCotree.mapIx_sim_eq Fin.val (Fin.ofNat n) (fun i => by simp) t

-- theorem PCotree.finToNat_eqv {n} {α} [BinderList α] {t t' : PCotree (Fin n) α} (h : t ≈ t') :
--   t.finToNat ≈ t'.finToNat :=
--   have _ := t.neZero;
--   PCotree.mapIx_eqv (fun i => by simp) h

--TODO: mapIx; mapIx

--TODO: fintag and friends;
  -- Fin n × ℕ ≅ ℕ
  -- ℕ × ℕ ≅ ℕ
  -- `Encodable` and associated lore
  -- General ℕ-ification

def Cotree (ι : Type _) (α : Type _) [BinderList α] : Type _ := Quotient (PCotree.setoid ι α)

def PCotree.toCotree {ι α} [BinderList α] (t : PCotree ι α) : Cotree ι α := ⟦t⟧

def Cotree.tag {ι α} [BinderList α] (t : Cotree ι α) : α :=
  Quotient.liftOn t (fun t => t.root.tag) fun _ _ h => h.tag

instance Cotree.instBinderList {ι α} [BinderList α] : BinderList (Cotree ι α) where
  numChildren t := numChildren t.tag
  binderList t := binderList t.tag
  getBinder t := getBinder t.tag
  getBinder_eq t := getBinder_eq t.tag

theorem PCotree.numChildren_toCotree {ι α} [BinderList α]
  (t : PCotree ι α) : numChildren t.toCotree = numChildren t := rfl

theorem PCotree.numChildren_quot {ι α} [BinderList α]
  (t : PCotree ι α) : numChildren (α := Cotree ι α) ⟦t⟧ = numChildren t := rfl

instance Cotree.instFlatChildren {ι α} [BinderList α]
  : FlatChildren (Cotree ι α) (Cotree ι α) where
  getDChild t := t.hrecOn (fun t j => PCotree.toCotree (getChild t j)) (
    fun a b h => by
      simp only [PCotree.numChildren_quot]
      rw [Fin.heq_fun_iff]
      · intro i
        apply Quotient.sound
        apply PCotree.eqv_children h i
      apply PCotree.eqv_numChildren h
  )

instance PCotree.instInhabited {ι α} [Inhabited α] [Inhabited ι] [BinderList α]
  : Inhabited (PCotree ι α) := ⟨default, fun _ => default⟩

instance Cotree.instInhabited {ι α} [Inhabited α] [Inhabited ι] [BinderList α]
  : Inhabited (Cotree ι α) := ⟨PCotree.instInhabited.default.toCotree⟩

theorem Cotree.neZero {n} {α} [BinderList α]
  (t : Cotree (Fin n) α) : NeZero n := by induction t using Quot.ind with | mk t => exact t.neZero

-- def Cotree.mapIx {ι₁ ι₂ α} [BinderList α]
--   (f : ι₁ → ι₂) (g : ι₂ → ι₁) (hfg : ∀ i, g (f i) = i)
--   (t : Cotree ι₁ α) : Cotree ι₂ α :=
--   Quotient.liftOn t (fun t => (t.mapIx f g).toCotree) fun _ _ h
--     => Quotient.sound <| PCotree.mapIx_eqv hfg h

-- @[simp]
-- theorem Cotree.mapIx_self {ι α} [BinderList α]
--   (f g : ι → ι) (hfg : ∀ i, g (f i) = i)
--   (t : Cotree ι α) :
--   t.mapIx f g hfg = t := by induction t using Quot.ind with | mk t =>
--   exact Quotient.sound (PCotree.mapIx_sim_eq f g hfg t).symm

-- def Cotree.finToNat {n} {α} [BinderList α] (t : Cotree (Fin n) α) : Cotree ℕ α :=
--   Quotient.liftOn t (fun t => t.finToNat.toCotree) fun _ _ h
--     => Quotient.sound <| PCotree.finToNat_eqv h

/-- A pre-cotree over a given partial address space -/
structure PCotree? (ι : Type _) (α : Type _) [NumChildren α] : Type _ where
  ix : ι
  getNode : ι → Option (Node α ι)

def PCotree?.Sim? {ι₁ ι₂ α β} [BinderList α] [BinderList β] (rel : α → β → Prop)
  (t₁ : PCotree? ι₁ α) (t₂ : PCotree? ι₂ β) : Prop
  := SimIx rel t₁.getNode t₂.getNode t₁.ix t₂.ix

theorem PCotree?.Sim?.symm {ι₁ ι₂ α} [BinderList α]
  {rel} [IsSymm α rel]
  {t₁ : PCotree? ι₁ α} {t₂ : PCotree? ι₂ α}
  (h : PCotree?.Sim? rel t₁ t₂) : PCotree?.Sim? rel t₂ t₁ :=
  SimIx.symm h

theorem PCotree?.Sim?.trans {ι₁ ι₂ ι₃ α} [BinderList α]
  {rel} [IsTrans α rel]
  {t₁ : PCotree? ι₁ α} {t₂ : PCotree? ι₂ α} {t₃ : PCotree? ι₃ α}
  (h1 : PCotree?.Sim? rel t₁ t₂)
  (h2 : PCotree?.Sim? rel t₂ t₃) : PCotree?.Sim? rel t₁ t₃ :=
  SimIx.trans h1 h2

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

instance PCotree?.instEmptyCollection {ι α} [Inhabited ι] [BinderList α]
  : EmptyCollection (PCotree? ι α) where
  emptyCollection := {
    ix := default,
    getNode := fun _ => none
  }

instance PCotree?.instInhabited {ι α} [Inhabited ι] [BinderList α]
  : Inhabited (PCotree? ι α) := ⟨∅⟩

def PCotree?.toCotree? {ι α} [BinderList α] (t : PCotree? ι α) : Cotree? ι α := ⟦t⟧

instance Cotree?.instEmptyCollection {ι α} [Inhabited ι] [BinderList α]
  : EmptyCollection (Cotree? ι α) where
  emptyCollection := PCotree?.toCotree? (∅ : PCotree? ι α)

instance Cotree?.instInhabited {ι α} [Inhabited ι] [BinderList α]
  : Inhabited (Cotree? ι α) := ⟨∅⟩

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

instance PFCotree.toFCotree {α} [BinderList α] (t : PFCotree α) : FCotree α := ⟦t⟧

instance PFCotree.instInhabited {α} [Inhabited α] [BinderList α]
  : Inhabited (PFCotree α) := ⟨{
    size := 1,
    cotree := default
  }⟩

instance FCotree.instInhabited {α} [Inhabited α] [BinderList α]
  : Inhabited (FCotree α) := ⟨PFCotree.toFCotree (default : PFCotree α)⟩

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

def PFCotree?.toFCotree? {α} [BinderList α] (t : PFCotree? α) : FCotree? α := ⟦t⟧

instance PFCotree?.instEmptyCollection {α} [Inhabited α] [BinderList α]
  : EmptyCollection (PFCotree? α) where
  emptyCollection := {
    size := 1,
    cotree := ∅
  }

instance PFCotree?.instInhabited {α} [Inhabited α] [BinderList α]
  : Inhabited (PFCotree? α) := ⟨∅⟩

instance FCotree?.instEmptyCollection {α} [Inhabited α] [BinderList α]
  : EmptyCollection (FCotree? α) where
  emptyCollection := PFCotree?.toFCotree? (∅ : PFCotree? α)

instance FCotree?.instInhabited {α} [Inhabited α] [BinderList α]
  : Inhabited (FCotree? α) := ⟨∅⟩

end Gt3
