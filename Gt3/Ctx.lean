import Gt3.Syntax.Basic

inductive Ctx : Type
| nil : Ctx
| cons (Γ : Ctx) (x : String) (A : Tm 0) : Ctx

@[simp]
def Ctx.len : Ctx → ℕ
| .nil => 0
| .cons Γ _ _ => len Γ + 1

@[simp]
def Ctx.dv : Ctx → Finset String
| .nil => ∅
| .cons Γ x _ => insert x (dv Γ)

theorem Ctx.dv_nil : nil.dv = ∅ := rfl

theorem Ctx.head_mem_dv {Γ : Ctx} {x A} : x ∈ (Γ.cons x A).dv := by simp

theorem Ctx.card_dv (Γ : Ctx) : Γ.dv.card ≤ Γ.len := by
  induction Γ with
  | nil => simp
  | cons Γ x A =>
    simp only [dv, len]
    have hΓ := Γ.dv.card_insert_le x
    omega

inductive Ctx.NoDup : Ctx → Prop
| nil : NoDup .nil
| cons (Γ : Ctx) (x : String) (A : Tm 0) : NoDup Γ → x ∉ dv Γ → NoDup (Ctx.cons Γ x A)

attribute [simp] Ctx.NoDup.nil

theorem Ctx.NoDup.card_dv {Γ : Ctx} (h : Ctx.NoDup Γ) : Γ.dv.card = Γ.len := by
  induction h with
  | nil => simp [len, dv]
  | cons Γ x A hnd hnotin ih =>
    simp only [dv, len]
    rw [Finset.card_insert_of_notMem hnotin, ih]

theorem Ctx.NoDup.of_card_dv {Γ : Ctx} (h : Γ.dv.card = Γ.len) : Ctx.NoDup Γ := by
  induction Γ with
  | nil => exact .nil
  | cons Γ x A I =>
    if hx : x ∈ Γ.dv then
      have hΓ := Γ.card_dv
      simp [Finset.card_insert_of_mem hx] at h
      omega
    else
      simp [Finset.card_insert_of_notMem hx] at h
      exact .cons _ _ _ (I h) hx

theorem Ctx.card_dv_eq_iff {Γ : Ctx} : Γ.dv.card = Γ.len ↔ Ctx.NoDup Γ
  := ⟨NoDup.of_card_dv, NoDup.card_dv⟩

inductive Ctx.Scoped : Ctx → Prop
| nil : Scoped .nil
| cons (Γ : Ctx) (x : String) (A : Tm 0) : Scoped Γ → A.fvs ⊆ dv Γ → Scoped (Ctx.cons Γ x A)

attribute [simp] Ctx.Scoped.nil

theorem Ctx.Scoped.tail {Γ x A} (h : Ctx.Scoped (Ctx.cons Γ x A)) : Ctx.Scoped Γ := by
  cases h; assumption

theorem Ctx.Scoped.head {Γ x A} (h : Ctx.Scoped (Ctx.cons Γ x A)) : A.fvs ⊆ Γ.dv := by
  cases h; assumption

theorem Ctx.Scoped.cons_iff {Γ x A} : Scoped (Ctx.cons Γ x A) ↔ Scoped Γ ∧ A.fvs ⊆ Γ.dv
  := ⟨fun h => ⟨h.tail, h.head⟩, fun ⟨hΓ, hA⟩ => hΓ.cons _ _ _ hA⟩

def Ctx.append : Ctx → Ctx → Ctx
| Γ, .nil => Γ
| Γ, .cons Δ x A => (append Γ Δ).cons x A

instance Ctx.instAppend : Append Ctx where
  append := Ctx.append

@[simp] theorem Ctx.append_nil (Γ : Ctx) : Γ ++ .nil = Γ := rfl

@[simp] theorem Ctx.append_cons (Γ Δ : Ctx) (x : String) (A : Tm 0) :
    Γ ++ (Δ.cons x A) = (Γ ++ Δ).cons x A := rfl

@[simp] theorem Ctx.nil_append (Δ : Ctx) : .nil ++ Δ = Δ := by induction Δ <;> simp [*]

theorem Ctx.append_assoc (Γ Δ Θ : Ctx) : (Γ ++ Δ) ++ Θ = Γ ++ (Δ ++ Θ) := by
  induction Θ generalizing Γ Δ <;> simp [*]

theorem Ctx.len_append (Γ Δ : Ctx) : (append Γ Δ).len = Γ.len + Δ.len := by
  induction Δ generalizing Γ <;> simp [append, len, Nat.add_assoc, *]

theorem Ctx.dv_append (Γ Δ : Ctx) : (append Γ Δ).dv = Γ.dv ∪ Δ.dv := by
  induction Δ generalizing Γ <;> simp [append, dv, *]

theorem Ctx.Scoped.append {Γ Δ : Ctx} (hΓ : Γ.Scoped) (hΔ : Δ.Scoped) : (Γ ++ Δ).Scoped := by
  induction hΔ with
  | nil => exact hΓ
  | cons Δ x A hscop hsub I =>
    constructor
    · assumption
    apply Finset.Subset.trans hsub
    simp [Ctx.dv_append]

theorem Ctx.NoDup.left {Γ Δ : Ctx} (h : (Γ ++ Δ).NoDup) : Γ.NoDup := by
  induction Δ generalizing Γ with
  | nil => exact h
  | cons => cases h; apply_assumption; assumption

theorem Ctx.NoDup.right {Γ Δ : Ctx} (h : (Γ ++ Δ).NoDup) : Δ.NoDup := by
  induction Δ generalizing Γ with
  | nil => exact .nil
  | cons Δ x A I =>
    cases h
    constructor
    · apply_assumption; assumption
    simp [dv_append] at *
    simp [*]

inductive Ctx.LookupT : Ctx → String → Tm 0 → Type
  | here (Γ : Ctx) (x : String) (A : Tm 0) : LookupT (Ctx.cons Γ x A) x A
  | there (Γ : Ctx) (x : String) (y : String) (A B : Tm 0) :
     LookupT Γ x A → x ≠ y → LookupT (Ctx.cons Γ y B) x A

inductive Ctx.Lookup : Ctx → String → Tm 0 → Prop
  | here (Γ : Ctx) (x : String) (A : Tm 0) : Lookup (Ctx.cons Γ x A) x A
  | there (Γ : Ctx) (x : String) (y : String) (A B : Tm 0) :
     Lookup Γ x A → x ≠ y → Lookup (Ctx.cons Γ y B) x A

attribute [simp] Ctx.Lookup.here

theorem Ctx.LookupT.toProp {Γ : Ctx} {x : String} {A : Tm 0}
  (h : Ctx.LookupT Γ x A) : Ctx.Lookup Γ x A
  := by induction h <;> constructor <;> assumption

def Ctx.LookupT.ix {Γ : Ctx} {x : String} {A : Tm 0} : Ctx.LookupT Γ x A → ℕ
  | .here _ _ _ => 0
  | .there _ _ _ _ _ h _ => h.ix + 1

theorem Ctx.Lookup.unique {Γ : Ctx} {x : String} {A B : Tm 0}
  (hA : Ctx.Lookup Γ x A) (hB : Ctx.Lookup Γ x B) : A = B := by
  induction hA <;> cases hB <;> first | rfl | contradiction | (apply_assumption; assumption)

theorem Ctx.LookupT.unique {Γ : Ctx} {x : String} {A B : Tm 0}
  (hA : Ctx.LookupT Γ x A) (hB : Ctx.LookupT Γ x B) : A = B := hA.toProp.unique hB.toProp

instance Ctx.LookupT.instSubsingleton {Γ : Ctx} {x : String} {A : Tm 0}
  : Subsingleton (Ctx.LookupT Γ x A) where
  allEq a b :=
    by induction a <;> cases b <;> first | rfl | contradiction | (congr; apply_assumption)

def Ctx.LookupT.prepend
  (Γ : Ctx) {Δ : Ctx} {x : String} {A : Tm 0}
  : Ctx.LookupT Δ x A → Ctx.LookupT (Γ ++ Δ) x A
  | .here _ _ _ => .here _ _ _
  | .there _ _ _ _ _ h _ => .there _ _ _ _ _ (prepend Γ h) ‹_›

theorem Ctx.Lookup.dv {Γ : Ctx} {x : String} {A : Tm 0} (h : Ctx.Lookup Γ x A) : x ∈ Γ.dv := by
  induction h <;> simp [Ctx.dv, *]

theorem Ctx.LookupT.dv {Γ : Ctx} {x : String} {A : Tm 0} (h : Ctx.LookupT Γ x A)
  : x ∈ Γ.dv := h.toProp.dv

theorem Ctx.Lookup.head {Γ : Ctx} {x : String} {A B : Tm 0}
  (h : (Γ.cons x A).Lookup x B) : A = B := by
  cases h with
  | here => rfl
  | there => contradiction

theorem Ctx.Lookup.head' {Γ : Ctx} {x y : String} {A B : Tm 0} (hx : x = y)
  (h : (Γ.cons y A).Lookup x B) : A = B := by cases hx; exact h.head

theorem Ctx.Lookup.tail {Γ : Ctx} {x y : String} {A B : Tm 0}
  (h : (Γ.cons y B).Lookup x A) (hx : x ≠ y) : Γ.Lookup x A := by
  cases h with
  | here => simp at hx
  | there => assumption

def Ctx.Lookup.choose {Γ x A} (h : Lookup Γ x A) : Ctx.LookupT Γ x A
  := match Γ, h with
  | .cons Γ y B, h => if hx : x = y then
      hx ▸ (h.head' hx) ▸ .here _ _ _
    else
      .there Γ x y A B (choose (h.tail hx)) hx

theorem Ctx.Lookup.exists_of_mem {Γ : Ctx} {x} (hx : x ∈ Γ.dv) : ∃ A, Lookup Γ x A := by
  induction Γ with
  | nil => simp at hx
  | cons Γ y A I =>
    if hy : x = y then
      cases hy; exact ⟨_, .here _ _ _⟩
    else
      simp [Ctx.dv, hy] at hx
      have ⟨B, I⟩ := I hx;
      exact ⟨B, I.there _ _ _ _ _ hy⟩

theorem Ctx.Scoped.lookup {Γ} (hΓ : Scoped Γ) {x A} (h : Lookup Γ x A) : A.fvs ⊆ Γ.dv := by
  induction h
  <;> cases hΓ
  <;> apply Finset.Subset.trans _ (Finset.subset_insert _ _)
  <;> apply_assumption
  assumption

def Ctx.LSub (Γ Δ : Ctx) : Prop := ∀x A, Ctx.Lookup Δ x A → Ctx.Lookup Γ x A

theorem Ctx.LSub.refl (Γ : Ctx) : Ctx.LSub Γ Γ := by intro x A h; exact h

theorem Ctx.LSub.trans {Γ Δ Θ : Ctx} (hΓΔ : Ctx.LSub Γ Δ) (hΔΘ : Ctx.LSub Δ Θ) : Ctx.LSub Γ Θ
  := by intro x A h; exact hΓΔ x A (hΔΘ x A h)

theorem Ctx.LSub.dv {Γ Δ} (h : LSub Γ Δ) : Δ.dv ⊆ Γ.dv := fun x hx =>
  have ⟨A, hA⟩ := Lookup.exists_of_mem hx
  (h x A hA).dv

theorem Ctx.LSub.cons {Γ Δ} (h : LSub Γ Δ) (x A) : LSub (Γ.cons x A) (Δ.cons x A)
  := fun y B hB => if hy : y = x then by cases hy; cases hB.head; constructor
  else by cases hB with
  | here => simp at hy
  | there _ _ _ _ _ w => exact .there _ _ _ _ _ (h _ _ w) hy

theorem Ctx.LSub.skip {Γ Δ} (h : LSub Γ Δ) {x} (hx : x ∉ Δ.dv) (A) : LSub (Γ.cons x A) Δ
  := fun y B hB => if hy : y = x then by
    cases hy; exact (hx hB.dv).elim
  else by
    apply Lookup.there
    · apply h; assumption
    · assumption

def Ctx.LEqv (Γ Δ : Ctx) : Prop := ∀x A, Ctx.Lookup Γ x A ↔ Ctx.Lookup Δ x A

theorem Ctx.LEqv.refl (Γ : Ctx) : Ctx.LEqv Γ Γ := by intro x A; rfl

theorem Ctx.LEqv.symm {Γ Δ : Ctx} (h : Ctx.LEqv Γ Δ) : Ctx.LEqv Δ Γ := by intro x A; rw [h x A]

theorem Ctx.LEqv.trans {Γ Δ Θ : Ctx} (hΓΔ : Ctx.LEqv Γ Δ) (hΔΘ : Ctx.LEqv Δ Θ) : Ctx.LEqv Γ Θ
  := by intro x A; rw [hΓΔ x A, hΔΘ x A]

theorem Ctx.LEqv.le {Γ Δ : Ctx} (h : Ctx.LEqv Γ Δ) : Ctx.LSub Γ Δ := by
  intro x A hΓ; exact (h x A).mpr hΓ

theorem Ctx.LEqv.ge {Γ Δ : Ctx} (h : Ctx.LEqv Γ Δ) : Ctx.LSub Δ Γ := by
  intro x A hΔ; exact (h x A).mp hΔ

theorem Ctx.LEqv.dv {Γ Δ} (h : LEqv Γ Δ) : Γ.dv = Δ.dv := le_antisymm h.ge.dv h.le.dv

theorem Ctx.LSub.antisymm {Γ Δ : Ctx}
  (hΓΔ : Ctx.LSub Γ Δ) (hΔΓ : Ctx.LSub Δ Γ) : Ctx.LEqv Γ Δ := by
  intro x A; constructor
  · intro hΔ; exact hΔΓ x A hΔ
  · intro hΓ; exact hΓΔ x A hΓ

theorem Ctx.Lookup.len_ne_zero {Γ : Ctx} {x : String} {A : Tm 0} (h : Ctx.Lookup Γ x A)
  : Γ.len ≠ 0 := by induction h <;> simp [Ctx.len, *]

theorem Ctx.LookupT.len_ne_zero {Γ : Ctx} {x : String} {A : Tm 0} (h : Ctx.LookupT Γ x A)
  : Γ.len ≠ 0 := h.toProp.len_ne_zero

inductive Ctx.SubT : Ctx → Ctx → Type
  | nil : SubT .nil .nil
  | cons {Γ Δ : Ctx} (hΓΔ : SubT Γ Δ) (x : String) (A : Tm 0)
    : SubT (Ctx.cons Γ x A) (Ctx.cons Δ x A)
  | skip {Γ Δ : Ctx} (hΓΔ : SubT Γ Δ) (x : String) (A : Tm 0)
    : x ∉ Γ.dv → SubT (Ctx.cons Γ x A) Δ

inductive Ctx.Sub : Ctx → Ctx → Prop
  | nil : Sub .nil .nil
  | cons {Γ Δ : Ctx} (hΓΔ : Sub Γ Δ) (x : String) (A : Tm 0)
    : Sub (Ctx.cons Γ x A) (Ctx.cons Δ x A)
  | skip {Γ Δ : Ctx} (hΓΔ : Sub Γ Δ) (x : String) (A : Tm 0)
    : x ∉ Γ.dv → Sub (Ctx.cons Γ x A) Δ

theorem Ctx.SubT.toProp {Γ Δ : Ctx} (h : Ctx.SubT Γ Δ) : Ctx.Sub Γ Δ
  := by induction h <;> constructor <;> assumption

theorem Ctx.Sub.dv {Γ Δ : Ctx} (h : Ctx.Sub Γ Δ) : Δ.dv ⊆ Γ.dv := by
  induction h with
  | skip =>
    simp only [Ctx.dv]
    rw [Finset.subset_insert_iff_of_notMem]
    · assumption
    apply Finset.not_mem_subset <;> assumption
  | _ => simp [Ctx.dv, *]

theorem Ctx.SubT.dv {Γ Δ : Ctx} (h : Ctx.SubT Γ Δ) : Δ.dv ⊆ Γ.dv := h.toProp.dv

instance Ctx.SubT.instSubsingleton {Γ Δ : Ctx} : Subsingleton (Ctx.SubT Γ Δ) where
  allEq a b := by
    induction a with
    | nil => cases b; rfl
    | skip a => cases b with
      | cons => have ha := a.dv; simp [Ctx.dv, Finset.insert_subset_iff, *] at ha
      | skip => congr; apply_assumption
    | cons => cases b with
      | skip b => have hb := b.dv; simp [Ctx.dv, Finset.insert_subset_iff, *] at hb
      | cons => congr; apply_assumption

def Ctx.SubT.lookup {Γ Δ : Ctx} {x A}
  : Ctx.SubT Γ Δ → Ctx.LookupT Δ x A → Ctx.LookupT Γ x A
  | .skip hΓΔ x A hx, hΔ
    => (hΓΔ.lookup hΔ).there _ _ _ _ _ (fun h => by cases h; exact hx (hΓΔ.dv hΔ.dv))
  | .cons hΓΔ x A, .here _ _ _ => .here _ _ _
  | .cons hΓΔ x A, .there _ _ _ _ _ hΔ hx => (hΓΔ.lookup hΔ).there _ _ _ _ _ hx

theorem Ctx.Sub.cons_mem {Γ Δ : Ctx} {x A} (h : Γ.Sub (Δ.cons x A)) : x ∈ Γ.dv
  := h.dv (by simp [Ctx.dv])

theorem Ctx.Sub.cons_eq {Γ Δ : Ctx} {x A B} (h : (Γ.cons x A).Sub (Δ.cons x B)) : A = B := by
  cases h with
  | cons => rfl
  | skip _ _ _ h => exfalso; apply h; apply Ctx.Sub.cons_mem; assumption

theorem Ctx.SubT.cons_mem {Γ Δ : Ctx} {x A} (h : Ctx.SubT Γ (Δ.cons x A)) : x ∈ Γ.dv
  := h.toProp.cons_mem

theorem Ctx.SubT.cons_eq {Γ Δ : Ctx} {x A B} (h : Ctx.SubT (Γ.cons x A) (Δ.cons x B)) : A = B
  := h.toProp.cons_eq

theorem Ctx.Sub.cons_tail {Γ Δ : Ctx} {x A B} (h : (Γ.cons x A).Sub (Δ.cons x B)) : Γ.Sub Δ
  := by cases h with
  | cons => assumption
  | skip _ _ _ h => exfalso; apply h; apply Ctx.Sub.cons_mem; assumption

def Ctx.SubT.cons_tail {Γ Δ : Ctx} {x A B} (h : Ctx.SubT (Γ.cons x A) (Δ.cons x B)) : Ctx.SubT Γ Δ
  := match h with
  | .cons h _ _ => h
  | .skip h _ _ hx => (hx h.cons_mem).elim

def Ctx.Sub.choose {Γ Δ : Ctx} (h : Ctx.Sub Γ Δ) : Ctx.SubT Γ Δ
  := match Γ, Δ, h with
  | .nil, .nil, _ => .nil
  | .cons Γ x A, .nil, h => .skip (choose (by cases h; assumption)) x A (by cases h; assumption)
  | .cons Γ x A, .cons Δ y B, h =>
    if hxy : x = y then
      hxy ▸ (hxy ▸ h).cons_eq ▸ .cons (choose ((hxy ▸ h).cons_tail)) x A
    else
      .skip (choose (by cases h <;> simp [*] at *)) x A (by cases h <;> simp [*] at *)

theorem Ctx.Sub.lookup {Γ Δ : Ctx} {x A}
  (hΓΔ : Ctx.Sub Γ Δ) (hΔ : Ctx.Lookup Δ x A) : Ctx.Lookup Γ x A
  := ((choose hΓΔ).lookup hΔ.choose).toProp

theorem Ctx.Sub.lsub {Γ Δ : Ctx} (h : Ctx.Sub Γ Δ) : Ctx.LSub Γ Δ := fun _ _ hx => h.lookup hx
