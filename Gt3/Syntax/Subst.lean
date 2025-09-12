import Gt3.Syntax.Erase

inductive Tm.Valid : ∀ {k}, Tm k → Prop
  | fv (x) : Valid (.fv x)
  | bv (i) : Valid (.bv i)
  | univ (ℓ) : Valid (.univ ℓ)
  | empty : Valid .empty
  | unit : Valid .unit
  | null : Valid .null
  | eqn {a b} : Valid a → Valid b → Valid (.eqn a b)
  | pi {A B} : Valid A → Valid B → Valid (.pi A B)
  | abs {A B b} : Valid A → Valid B → Valid b → Valid (.abs A B b)
  | app {f a} : Valid f → Valid a → Valid (.app f a)
  | sigma {A B} : Valid A → Valid B → Valid (.sigma A B)
  | pair {a b} : Valid a → Valid b → Valid (.pair a b)
  | fst {p} : Valid p → Valid (.fst p)
  | snd {p} : Valid p → Valid (.snd p)
  | dite {A φ l r} : Valid A → Valid φ → Valid l → Valid r → Valid (.dite A φ l r)
  | trunc {A} : Valid A → Valid (.trunc A)
  | choose {A φ} : Valid A → Valid φ → Valid (.choose A φ)
  | has_ty {A a} : Valid A → Valid a → Valid (.has_ty A a)

attribute [simp] Tm.Valid.fv Tm.Valid.bv Tm.Valid.univ Tm.Valid.empty Tm.Valid.unit Tm.Valid.null

@[simp]
theorem Tm.Valid.eqn_iff {k} {a b : Tm k} : Valid (.eqn a b) ↔ Valid a ∧ Valid b
  := ⟨fun h => by cases h; simp [*], fun h => by cases h; constructor <;> assumption⟩

@[simp]
theorem Tm.Valid.pi_iff {k} {A : Tm k} {B : Tm (k + 1)} : Valid (.pi A B) ↔ Valid A ∧ Valid B
  := ⟨fun h => by cases h; simp [*], fun h => by cases h; constructor <;> assumption⟩

@[simp]
theorem Tm.Valid.abs_iff {k} {A : Tm k} {B b : Tm (k + 1)}
  : Valid (.abs A B b) ↔ Valid A ∧ Valid B ∧ Valid b
:= ⟨fun h => by cases h; simp [*], fun h => by constructor <;> simp [*]⟩

@[simp]
theorem Tm.Valid.app_iff {k} {f a : Tm k} : Valid (.app f a) ↔ Valid f ∧ Valid a
  := ⟨fun h => by cases h; simp [*], fun h => by cases h; constructor <;> assumption⟩

@[simp]
theorem Tm.Valid.sigma_iff {k} {A : Tm k} {B : Tm (k + 1)}
  : Valid (.sigma A B) ↔ Valid A ∧ Valid B
  := ⟨fun h => by cases h; simp [*], fun h => by cases h; constructor <;> assumption⟩

@[simp]
theorem Tm.Valid.pair_iff {k} {a b : Tm k} : Valid (.pair a b) ↔ Valid a ∧ Valid b
  := ⟨fun h => by cases h; simp [*], fun h => by cases h; constructor <;> assumption⟩

@[simp]
theorem Tm.Valid.fst_iff {k} {p : Tm k} : Valid (.fst p) ↔ Valid p
  := ⟨fun h => by cases h; assumption, fun h => by constructor; assumption⟩

@[simp]
theorem Tm.Valid.snd_iff {k} {p : Tm k} : Valid (.snd p) ↔ Valid p
  := ⟨fun h => by cases h; assumption, fun h => by constructor; assumption⟩

@[simp]
theorem Tm.Valid.dite_iff {k} {A φ : Tm k} {l r : Tm (k + 1)}
  : Valid (.dite A φ l r) ↔ Valid A ∧ Valid φ ∧ Valid l ∧ Valid r
  := ⟨fun h => by cases h; simp [*], fun h => by constructor <;> simp [*]⟩

@[simp]
theorem Tm.Valid.trunc_iff {k} {A : Tm k} : Valid (.trunc A) ↔ Valid A
  := ⟨fun h => by cases h; assumption, fun h => by constructor; assumption⟩

@[simp]
theorem Tm.Valid.choose_iff {k} {A : Tm k} {φ : Tm (k + 1)}
  : Valid (.choose A φ) ↔ Valid A ∧ Valid φ
  := ⟨fun h => by cases h; simp [*], fun h => by cases h; constructor <;> assumption⟩

@[simp]
theorem Tm.Valid.has_ty_iff {k} {A a : Tm k} : Valid (.has_ty A a) ↔ Valid A ∧ Valid a
  := ⟨fun h => by cases h; simp [*], fun h => by cases h; constructor <;> assumption⟩

@[simp]
theorem Tm.Valid.invalid_iff {k} : ¬Valid (.invalid (k := k)) := fun h => by cases h

theorem Tm.open_valid_iff {k} (a : Tm (k + 1)) (x : String) : (a.open x).Valid ↔ a.Valid
  := by induction a using succIndOn with
  | bv i => cases i using Fin.lastCases <;> simp [Tm.open, *]
  | _ => simp [*]

theorem Tm.Valid.of_open {k} {a : Tm (k + 1)} {x} (h : Valid (a.open x)) : Valid a
  := (a.open_valid_iff x).mp h

theorem Tm.Valid.open {k} {a : Tm (k + 1)} (h : Valid a) (x) : Valid (a.open x)
  := (a.open_valid_iff x).mpr h

theorem Tm.forall_open_valid_iff {k} (a : Tm (k + 1)) : (∀x, (a.open x).Valid) ↔ a.Valid
  := by simp [Tm.open_valid_iff]

theorem Tm.forall_cf_open_valid_iff {k} (a : Tm (k + 1)) (L : Finset String)
  : (∀x ∉ L, (a.open x).Valid) ↔ a.Valid
  := ⟨fun h => have ⟨x, hx⟩ := L.exists_notMem; (h x hx).of_open, fun h x _ => h.open x⟩

theorem Tm.Valid.unclamp {k} {a : Tm k} (h : Valid (a.erase.clamp k)) : Valid a := by
  induction a <;> simp at * <;> simp [*]

theorem Tm.Valid.bvi {k r} {a : Tm k} (h : Valid (a.erase.clamp r)) : a.bvi ≤ r := by
  induction a generalizing r with
  | bv i =>
    simp only [erase, OTm.clamp] at h
    split at h
    · simp [Tm.bvi]; omega
    · cases h
  | _ =>
    simp [Tm.bvi] at * <;> cases h <;>
    (try constructorm* _ ∧ _) <;>
    apply_assumption <;> assumption

inductive Tm.Lstn : ∀ {l r}, Tm l → Tm r → Prop
  | refl : ∀ {l} (a : Tm l), Lstn a a
  | lst {l r} {a : Tm l} {a' : Tm (r + 1)}
    (h : Lstn a a') (v) : Lstn a (a'.lst v)

theorem Tm.Lstn.bounds {l r} {a : Tm l} {a' : Tm r} (h : Lstn a a') : r ≤ l
  := by induction h <;> omega

theorem Tm.Lstn.zero {a a' : Tm 0}
  (h : Lstn a a') : a = a' := by cases h with
  | refl => rfl
  | lst h => cases h.bounds

theorem Tm.Lstn.bvi_le {l r}
  {a : Tm l} {a' : Tm r} (h : Lstn a a') : a'.bvi ≤ a.bvi := by induction h with
  | refl => simp
  | lst h v I => rename_i a a'; have h' := a'.lst_bvi_le v; omega

theorem Tm.Lstn.erase_bvi {l r}
  {a : Tm l} {a' : Tm r} (h : Lstn a a') (ha : a.bvi ≤ r)
  : a.erase = a'.erase := by induction h with
  | refl => simp
  | lst h v I =>
    rename_i a a'
    rw [Tm.erase_lst, OTm.lst_bvi, I]
    · omega
    have h := h.bvi_le
    rw [bvi_erase]; omega

theorem Tm.Lstn.clamped_valid {l r}
  {a : Tm l} {a' : Tm r} (h : Lstn a a') (ha : Valid (a.erase.clamp r))
  : a.erase.clamp r = a' := by
  apply Tm.erase_injective
  rw [OTm.erase_clamp_bvi_le, h.erase_bvi] <;> convert ha.bvi
  simp

inductive Tm.LstBar : ∀ {l r}, Tm l → Tm l → Tm r → Tm r → Prop
  | refl : ∀ {l} (a b : Tm l), LstBar a b a b
  | lst {l r} {a b : Tm l} {a' b' : Tm (r + 1)}
    (h : LstBar a b a' b') (v) : LstBar a b (a'.lst v) (b'.lst v)

theorem Tm.LstBar.open {l r} {a b : Tm l} {a' b' : Tm (r + 1)}
  (h : LstBar a b a' b') (x) : LstBar a b (a'.open x) (b'.open x)
  := by convert h.lst (.fv x) <;> simp only [lst_fv]

theorem Tm.LstBar.lhs {l r} {a b : Tm l} {a' b' : Tm r} (h : LstBar a b a' b') : Lstn a a'
  := by induction h <;> constructor; assumption

theorem Tm.LstBar.rhs {l r} {a b : Tm l} {a' b' : Tm r} (h : LstBar a b a' b') : Lstn b b'
  := by induction h <;> constructor; assumption

theorem Tm.LstBar.bounds {l r} {a b : Tm l} {a' b' : Tm r}
  (h : LstBar a b a' b') : r ≤ l := h.lhs.bounds

theorem Tm.LstBar.zero_left {a b a' b' : Tm 0}
  (h : LstBar a b a' b') : a = a' := h.lhs.zero

theorem Tm.LstBar.zero_right {a b a' b' : Tm 0}
  (h : LstBar a b a' b') : b = b' := h.rhs.zero
