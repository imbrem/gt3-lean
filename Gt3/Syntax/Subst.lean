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
  | abs {A b} : Valid A → Valid b → Valid (.abs A b)
  | app {f a} : Valid f → Valid a → Valid (.app f a)
  | sigma {A B} : Valid A → Valid B → Valid (.sigma A B)
  | pair {a b} : Valid a → Valid b → Valid (.pair a b)
  | fst {p} : Valid p → Valid (.fst p)
  | snd {p} : Valid p → Valid (.snd p)
  | dite {φ l r} : Valid φ → Valid l → Valid r → Valid (.dite φ l r)
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
theorem Tm.Valid.abs_iff {k} {A : Tm k} {b : Tm (k + 1)}
  : Valid (.abs A b) ↔ Valid A ∧ Valid b
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
theorem Tm.Valid.dite_iff {k} {φ : Tm k} {l r : Tm (k + 1)}
  : Valid (.dite φ l r) ↔ Valid φ ∧ Valid l ∧ Valid r
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

inductive Tm.Lstn {l} (a : Tm l) : ∀ {r}, Tm r → Prop
  | refl : Lstn a a
  | lst {r} {a' : Tm (r + 1)}
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

theorem Tm.Lstn.fv {l r x a} (h : Lstn (l := l) (r := r) (.fv x) a) : a = .fv x := by
  induction h <;> simp [*]

theorem Tm.Lstn.univ {l r ℓ a} (h : Lstn (l := l) (r := r) (.univ ℓ) a) : a = .univ ℓ :=
  by induction h <;> simp [*]

theorem Tm.Lstn.empty {l r a} (h : Lstn (l := l) (r := r) .empty a) : a = .empty :=
  by induction h <;> simp [*]

theorem Tm.Lstn.unit {l r a} (h : Lstn (l := l) (r := r) .unit a) : a = .unit :=
  by induction h <;> simp [*]

theorem Tm.Lstn.null {l r a} (h : Lstn (l := l) (r := r) .null a) : a = .null :=
  by induction h <;> simp [*]

theorem Tm.Lstn.eqn {l r a b w} (h : Lstn (l := l) (r := r) (.eqn a b) w)
  : ∃a' b', w = .eqn a' b' ∧ Lstn a a' ∧ Lstn b b' :=
  by induction h with
  | refl => exact ⟨a, b, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨a', b', he, ha', hb'⟩ := I
    exact ⟨a'.lst v, b'.lst v, by simp [he], ha'.lst v, hb'.lst v⟩

theorem Tm.Lstn.pi {l r A B w} (h : Lstn (l := l) (r := r) (.pi A B) w)
  : ∃A' B', w = .pi A' B' ∧ Lstn A A' ∧ Lstn B B' :=
  by induction h with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨A', B', he, hA', hB'⟩ := I
    exact ⟨A'.lst v, B'.lst v, by simp [he], hA'.lst v, hB'.lst v⟩

theorem Tm.Lstn.abs {l r A b w} (h : Lstn (l := l) (r := r) (.abs A b) w)
  : ∃A' b', w = .abs A' b' ∧ Lstn A A' ∧ Lstn b b' :=
  by induction h with
  | refl => exact ⟨A, b, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨A', b', he, hA', hb'⟩ := I
    exact ⟨A'.lst v, b'.lst v, by simp [he], hA'.lst v, hb'.lst v⟩

theorem Tm.Lstn.app {l r f a w} (h : Lstn (l := l) (r := r) (.app f a) w)
  : ∃f' a', w = .app f' a' ∧ Lstn f f' ∧ Lstn a a' :=
  by induction h with
  | refl => exact ⟨f, a, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨f', a', he, hf', ha'⟩ := I
    exact ⟨f'.lst v, a'.lst v, by simp [he], hf'.lst v, ha'.lst v⟩

theorem Tm.Lstn.sigma {l r A B w} (h : Lstn (l := l) (r := r) (.sigma A B) w)
  : ∃A' B', w = .sigma A' B' ∧ Lstn A A' ∧ Lstn B B' :=
  by induction h with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨A', B', he, hA', hB'⟩ := I
    exact ⟨A'.lst v, B'.lst v, by simp [he], hA'.lst v, hB'.lst v⟩

theorem Tm.Lstn.pair {l r a b w} (h : Lstn (l := l) (r := r) (.pair a b) w)
  : ∃a' b', w = .pair a' b' ∧ Lstn a a' ∧ Lstn b b' :=
  by induction h with
  | refl => exact ⟨a, b, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨a', b', he, ha', hb'⟩ := I
    exact ⟨a'.lst v, b'.lst v, by simp [he], ha'.lst v, hb'.lst v⟩

theorem Tm.Lstn.fst {l r p w} (h : Lstn (l := l) (r := r) (.fst p) w)
  : ∃p', w = .fst p' ∧ Lstn p p' :=
  by induction h with
  | refl => exact ⟨p, rfl, .refl⟩
  | lst h v I =>
    have ⟨p', he, hp'⟩ := I
    exact ⟨p'.lst v, by simp [he], hp'.lst v⟩

theorem Tm.Lstn.snd {l r p w} (h : Lstn (l := l) (r := r) (.snd p) w)
  : ∃p', w = .snd p' ∧ Lstn p p' :=
  by induction h with
  | refl => exact ⟨p, rfl, .refl⟩
  | lst h v I =>
    have ⟨p', he, hp'⟩ := I
    exact ⟨p'.lst v, by simp [he], hp'.lst v⟩

theorem Tm.Lstn.dite {l r φ t e w} (h : Lstn (l := l) (r := r) (.dite φ t e) w)
  : ∃φ' t' e', w = .dite φ' t' e' ∧ Lstn φ φ' ∧ Lstn t t' ∧ Lstn e e' :=
  by induction h with
  | refl => exact ⟨φ, t, e, rfl, .refl, .refl, .refl⟩
  | lst h v I =>
    have ⟨φ', t', e', he, hφ', ht', he'⟩ := I
    exact ⟨φ'.lst v, t'.lst v, e'.lst v, by simp [he], hφ'.lst v, ht'.lst v, he'.lst v⟩

theorem Tm.Lstn.trunc {l r A w} (h : Lstn (l := l) (r := r) (.trunc A) w)
  : ∃A', w = .trunc A' ∧ Lstn A A' :=
  by induction h with
  | refl => exact ⟨A, rfl, .refl⟩
  | lst h v I =>
    have ⟨A', he, hA'⟩ := I
    exact ⟨A'.lst v, by simp [he], hA'.lst v⟩

theorem Tm.Lstn.choose {l r A φ w} (h : Lstn (l := l) (r := r) (.choose A φ) w)
  : ∃A' φ', w = .choose A' φ' ∧ Lstn A A' ∧ Lstn φ φ' :=
  by induction h with
  | refl => exact ⟨A, φ, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨A', φ', he, hA', hφ'⟩ := I
    exact ⟨A'.lst v, φ'.lst v, by simp [he], hA'.lst v, hφ'.lst v⟩

theorem Tm.Lstn.has_ty {l r A a w} (h : Lstn (l := l) (r := r) (.has_ty A a) w)
  : ∃A' a', w = .has_ty A' a' ∧ Lstn A A' ∧ Lstn a a' :=
  by induction h with
  | refl => exact ⟨A, a, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨A', a', he, hA', ha'⟩ := I
    exact ⟨A'.lst v, a'.lst v, by simp [he], hA'.lst v, ha'.lst v⟩

theorem Tm.Lstn.invalid {l r a} (h : Lstn (l := l) (r := r) .invalid a) : a = .invalid :=
  by induction h <;> simp [*]

inductive Tm.LstBar {l} (a b : Tm l) : ∀ {r}, Tm r → Tm r → Prop
  | refl : LstBar a b a b
  | lst {r} {a' b' : Tm (r + 1)}
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

theorem Tm.LstBar.bv {l r i a b}
  (h : LstBar (l := l) (r := r) (.bv i) (.bv i) a b)
  : a = b := by induction h <;> simp [*]

theorem Tm.LstBar.fv {l r x a b}
  (h : LstBar (l := l) (r := r) (.fv x) (.fv x) a b)
  : a = .fv x ∧ b = .fv x := by simp [h.lhs.fv, h.rhs.fv]

theorem Tm.LstBar.univ {l r ℓ a b}
  (h : LstBar (l := l) (r := r) (.univ ℓ) (.univ ℓ) a b) : a = .univ ℓ ∧ b = .univ ℓ :=
  by simp [h.lhs.univ, h.rhs.univ]

theorem Tm.LstBar.empty {l r a b}
  (h : LstBar (l := l) (r := r) .empty .empty a b) : a = .empty ∧ b = .empty :=
  by simp [h.lhs.empty, h.rhs.empty]

theorem Tm.LstBar.unit {l r a b}
  (h : LstBar (l := l) (r := r) .unit .unit a b) : a = .unit ∧ b = .unit :=
  by simp [h.lhs.unit, h.rhs.unit]

theorem Tm.LstBar.null {l r a b}
  (h : LstBar (l := l) (r := r) .null .null a b) : a = .null ∧ b = .null :=
  by simp [h.lhs.null, h.rhs.null]

theorem Tm.LstBar.eqn {l r al bl ar br wl wr}
  (h : LstBar (l := l) (r := r) (.eqn al bl) (.eqn ar br) wl wr)
  : ∃ al' bl' ar' br',
      wl = .eqn al' bl' ∧ wr = .eqn ar' br'
      ∧ LstBar al ar al' ar' ∧ LstBar bl br bl' br'  :=
  by induction h with
  | refl => exact ⟨al, bl, ar, br, rfl, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨al', bl', ar', br', hl, hr, ha', hb'⟩ := I
    exact ⟨
      al'.lst v, bl'.lst v, ar'.lst v, br'.lst v,
      by simp [hl], by simp [hr], ha'.lst v, hb'.lst v⟩

theorem Tm.LstBar.pi {l r Al Bl Ar Br wl wr}
  (h : LstBar (l := l) (r := r) (.pi Al Bl) (.pi Ar Br) wl wr)
  : ∃ Al' Bl' Ar' Br',
      wl = .pi Al' Bl' ∧ wr = .pi Ar' Br'
      ∧ LstBar Al Ar Al' Ar' ∧ LstBar Bl Br Bl' Br'  :=
  by induction h with
  | refl => exact ⟨Al, Bl, Ar, Br, rfl, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨Al', Bl', Ar', Br', hl, hr, hA', hB'⟩ := I
    exact ⟨
      Al'.lst v, Bl'.lst v, Ar'.lst v, Br'.lst v,
      by simp [hl], by simp [hr], hA'.lst v, hB'.lst v⟩

theorem Tm.LstBar.abs {l r Al bl Ar br wl wr}
  (h : LstBar (l := l) (r := r) (.abs Al bl) (.abs Ar br) wl wr)
  : ∃ Al' bl' Ar' br',
      wl = .abs Al' bl' ∧ wr = .abs Ar' br'
      ∧ LstBar Al Ar Al' Ar' ∧ LstBar bl br bl' br'  :=
  by induction h with
  | refl => exact ⟨Al, bl, Ar, br, rfl, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨Al', bl', Ar', br', hl, hr, hA', hb'⟩ := I
    exact ⟨
      Al'.lst v, bl'.lst v, Ar'.lst v, br'.lst v,
      by simp [hl], by simp [hr], hA'.lst v, hb'.lst v⟩

theorem Tm.LstBar.app {l r fl al fr ar wl wr}
  (h : LstBar (l := l) (r := r) (.app fl al) (.app fr ar) wl wr)
  : ∃ fl' al' fr' ar',
      wl = .app fl' al' ∧ wr = .app fr' ar'
      ∧ LstBar fl fr fl' fr' ∧ LstBar al ar al' ar'  :=
  by induction h with
  | refl => exact ⟨fl, al, fr, ar, rfl, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨fl', al', fr', ar', hl, hr, hf', ha'⟩ := I
    exact ⟨
      fl'.lst v, al'.lst v, fr'.lst v, ar'.lst v,
      by simp [hl], by simp [hr], hf'.lst v, ha'.lst v⟩

theorem Tm.LstBar.sigma {l r Al Bl Ar Br wl wr}
  (h : LstBar (l := l) (r := r) (.sigma Al Bl) (.sigma Ar Br) wl wr)
  : ∃ Al' Bl' Ar' Br',
      wl = .sigma Al' Bl' ∧ wr = .sigma Ar' Br'
      ∧ LstBar Al Ar Al' Ar' ∧ LstBar Bl Br Bl' Br'  :=
  by induction h with
  | refl => exact ⟨Al, Bl, Ar, Br, rfl, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨Al', Bl', Ar', Br', hl, hr, hA', hB'⟩ := I
    exact ⟨
      Al'.lst v, Bl'.lst v, Ar'.lst v, Br'.lst v,
      by simp [hl], by simp [hr], hA'.lst v, hB'.lst v⟩

theorem Tm.LstBar.pair {l r al bl ar br wl wr}
  (h : LstBar (l := l) (r := r) (.pair al bl) (.pair ar br) wl wr)
  : ∃ al' bl' ar' br',
      wl = .pair al' bl' ∧ wr = .pair ar' br'
      ∧ LstBar al ar al' ar' ∧ LstBar bl br bl' br'  :=
  by induction h with
  | refl => exact ⟨al, bl, ar, br, rfl, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨al', bl', ar', br', hl, hr, ha', hb'⟩ := I
    exact ⟨
      al'.lst v, bl'.lst v, ar'.lst v, br'.lst v,
      by simp [hl], by simp [hr], ha'.lst v, hb'.lst v⟩

theorem Tm.LstBar.fst {l r pl pr wl wr}
  (h : LstBar (l := l) (r := r) (.fst pl) (.fst pr) wl wr)
  : ∃ pl' pr',
      wl = .fst pl' ∧ wr = .fst pr'
      ∧ LstBar pl pr pl' pr'  :=
  by induction h with
  | refl => exact ⟨pl, pr, rfl, rfl, .refl⟩
  | lst h v I =>
    have ⟨pl', pr', hl, hr, hp'⟩ := I
    exact ⟨
      pl'.lst v, pr'.lst v,
      by simp [hl], by simp [hr], hp'.lst v⟩

theorem Tm.LstBar.snd {l r pl pr wl wr}
  (h : LstBar (l := l) (r := r) (.snd pl) (.snd pr) wl wr)
  : ∃ pl' pr',
      wl = .snd pl' ∧ wr = .snd pr'
      ∧ LstBar pl pr pl' pr'  :=
  by induction h with
  | refl => exact ⟨pl, pr, rfl, rfl, .refl⟩
  | lst h v I =>
    have ⟨pl', pr', hl, hr, hp'⟩ := I
    exact ⟨
      pl'.lst v, pr'.lst v,
      by simp [hl], by simp [hr], hp'.lst v⟩

theorem Tm.LstBar.dite {l r φl tl el φr tr er wl wr}
  (h : LstBar (l := l) (r := r) (.dite φl tl el) (.dite φr tr er) wl wr)
  : ∃ φl' tl' el' φr' tr' er',
      wl = .dite φl' tl' el' ∧ wr = .dite φr' tr' er'
      ∧ LstBar φl φr φl' φr' ∧ LstBar tl tr tl' tr' ∧ LstBar el er el' er'  :=
  by induction h with
  | refl => exact ⟨φl, tl, el, φr, tr, er, rfl, rfl, .refl, .refl, .refl⟩
  | lst h v I =>
    have ⟨φl', tl', el', φr', tr', er', hl, hr, hφ', ht', he'⟩ := I
    exact ⟨
      φl'.lst v, tl'.lst v, el'.lst v, φr'.lst v, tr'.lst v, er'.lst v,
      by simp [hl], by simp [hr], hφ'.lst v, ht'.lst v, he'.lst v⟩

theorem Tm.LstBar.trunc {l r Al Ar wl wr}
  (h : LstBar (l := l) (r := r) (.trunc Al) (.trunc Ar) wl wr)
  : ∃ Al' Ar',
      wl = .trunc Al' ∧ wr = .trunc Ar'
      ∧ LstBar Al Ar Al' Ar'  :=
  by induction h with
  | refl => exact ⟨Al, Ar, rfl, rfl, .refl⟩
  | lst h v I =>
    have ⟨Al', Ar', hl, hr, hA'⟩ := I
    exact ⟨
      Al'.lst v, Ar'.lst v,
      by simp [hl], by simp [hr], hA'.lst v⟩

theorem Tm.LstBar.choose {l r Al φl Ar φr wl wr}
  (h : LstBar (l := l) (r := r) (.choose Al φl) (.choose Ar φr) wl wr)
  : ∃ Al' φl' Ar' φr',
      wl = .choose Al' φl' ∧ wr = .choose Ar' φr'
      ∧ LstBar Al Ar Al' Ar' ∧ LstBar φl φr φl' φr'  :=
  by induction h with
  | refl => exact ⟨Al, φl, Ar, φr, rfl, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨Al', φl', Ar', φr', hl, hr, hA', hφ'⟩ := I
    exact ⟨
      Al'.lst v, φl'.lst v, Ar'.lst v, φr'.lst v,
      by simp [hl], by simp [hr], hA'.lst v, hφ'.lst v⟩

theorem Tm.LstBar.has_ty {l r Al al Ar ar wl wr}
  (h : LstBar (l := l) (r := r) (.has_ty Al al) (.has_ty Ar ar) wl wr)
  : ∃ Al' al' Ar' ar',
      wl = .has_ty Al' al' ∧ wr = .has_ty Ar' ar'
      ∧ LstBar Al Ar Al' Ar' ∧ LstBar al ar al' ar'  :=
  by induction h with
  | refl => exact ⟨Al, al, Ar, ar, rfl, rfl, .refl, .refl⟩
  | lst h v I =>
    have ⟨Al', al', Ar', ar', hl, hr, hA', ha'⟩ := I
    exact ⟨
      Al'.lst v, al'.lst v, Ar'.lst v, ar'.lst v,
      by simp [hl], by simp [hr], hA'.lst v, ha'.lst v⟩

theorem Tm.LstBar.invalid {l r wl wr}
  (h : LstBar (l := l) (r := r) .invalid .invalid wl wr) : wl = .invalid ∧ wr = .invalid :=
  by simp [h.lhs.invalid, h.rhs.invalid]

theorem Tm.LstBar.split {l r} {a b : Tm l} {a' b' : Tm r}
  (h : LstBar a b a' b') (c : Tm l)
  : ∃c', LstBar a c a' c' ∧ LstBar c b c' b'
  := by induction h with
  | refl => exact ⟨c, .refl, .refl⟩
  | lst h v I => have ⟨c, hac, hcb⟩ := I; exact ⟨c.lst v, hac.lst v, hcb.lst v⟩
