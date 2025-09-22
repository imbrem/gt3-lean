import Gt3.RwEq.Basic
import Gt3.HasTy.Inversion

def Ctx.KJEq (Γ : Ctx) (A a b : OTm) : Prop := JEq Γ (A.clamp 0) (a.clamp 0) (b.clamp 0)

theorem Ctx.KJEq.get {Γ A a b} (h : KJEq Γ A a b)
  : JEq Γ (A.clamp 0) (a.clamp 0) (b.clamp 0) := h

def Ctx.KIsTy (Γ : Ctx) (a : OTm) : Prop := IsTy Γ (a.clamp 0)

theorem Ctx.KIsTy.univ {Γ ℓ} (h : Ok Γ) : KIsTy Γ (.univ ℓ) := IsTy.univ h

theorem Ctx.KIsTy.empty {Γ} (h : Ok Γ) : KIsTy Γ .empty := IsTy.empty h

theorem Ctx.KIsTy.unit {Γ} (h : Ok Γ) : KIsTy Γ .unit := IsTy.unit h

theorem Ctx.KIsTy.nats {Γ} (h : Ok Γ) : KIsTy Γ .nats := IsTy.nats h

theorem Ctx.KIsTy.get {Γ a} (h : KIsTy Γ a)
  : IsTy Γ (a.clamp 0) := h

def Ctx.KTyEq (Γ : Ctx) (a b : OTm) : Prop := TyEq Γ (a.clamp 0) (b.clamp 0)

theorem Ctx.KTyEq.get {Γ A B} (h : KTyEq Γ A B)
  : TyEq Γ (A.clamp 0) (B.clamp 0) := h

def Ctx.KIsWf (Γ : Ctx) (a : OTm) : Prop := IsWf Γ (a.clamp 0)

theorem Ctx.KIsWf.lc {Γ a} (h : KIsWf Γ a) : a.bvi = 0 := by convert h.valid.otm_bvi using 0; simp

theorem Ctx.KIsTy.wf {Γ A} (h : KIsTy Γ A) : KIsWf Γ A := h.get.wf

theorem Ctx.KIsTy.lc {Γ A} (h : KIsTy Γ A) : A.bvi = 0 := h.wf.lc

theorem Ctx.KIsWf.univ {Γ ℓ} (h : Ok Γ) : KIsWf Γ (.univ ℓ) := (IsTy.univ h).wf

theorem Ctx.KIsWf.empty {Γ} (h : Ok Γ) : KIsWf Γ .empty := (IsTy.empty h).wf

theorem Ctx.KIsWf.unit {Γ} (h : Ok Γ) : KIsWf Γ .unit := (IsTy.unit h).wf

theorem Ctx.KIsWf.null {Γ} (h : Ok Γ) : KIsWf Γ .null := (JEq.null h).lhs_is_wf

theorem Ctx.KIsWf.nats {Γ} (h : Ok Γ) : KIsWf Γ .nats := (IsTy.nats h).wf

theorem Ctx.KIsWf.zero {Γ} (h : Ok Γ) : KIsWf Γ .zero := (JEq.zero h).lhs_is_wf

theorem Ctx.KIsWf.get {Γ a} (h : KIsWf Γ a)
  : IsWf Γ (a.clamp 0) := h

def Ctx.KHasTy (Γ : Ctx) (A a : OTm) : Prop := HasTy Γ (A.clamp 0) (a.clamp 0)

theorem Ctx.KHasTy.get {Γ A a} (h : KHasTy Γ A a)
  : HasTy Γ (A.clamp 0) (a.clamp 0) := h

theorem Ctx.KHasTy.is_wf {Γ A a} (h : KHasTy Γ A a) : KIsWf Γ a := h.get.is_wf

theorem Ctx.KHasTy.regular {Γ A a} (h : KHasTy Γ A a) : KIsTy Γ A := h.get.regular

def Ctx.KWEq (Γ : Ctx) (a b : OTm) : Prop := WfEq Γ (a.clamp 0) (b.clamp 0)

theorem Ctx.KWEq.get {Γ a b} (h : KWEq Γ a b)
  : WfEq Γ (a.clamp 0) (b.clamp 0) := h

theorem Ctx.KWEq.lhs {Γ a b} (h : KWEq Γ a b) : KIsWf Γ a := h.get.lhs

theorem Ctx.KWEq.rhs {Γ a b} (h : KWEq Γ a b) : KIsWf Γ b := h.get.rhs

inductive Ctx.KEq (Γ : Ctx) : OTm → OTm → Prop
  | fv (x) : KEq Γ (.fv x) (.fv x)
  | bv (i) : KEq Γ (.bv i) (.bv i)
  | univ (ℓ) : KEq Γ (.univ ℓ) (.univ ℓ)
  | empty : KEq Γ .empty .empty
  | unit : KEq Γ .unit .unit
  | null : KEq Γ .null .null
  | eqn {a a' b b'} : KEq Γ a a' → KEq Γ b b' → KEq Γ (.eqn a b) (.eqn a' b')
  | pi {A A' B B'} : KEq Γ A A' → KEq Γ B B' → KEq Γ (.pi A B) (.pi A' B')
  | sigma {A A' B B'} : KEq Γ A A' → KEq Γ B B' → KEq Γ (.sigma A B) (.sigma A' B')
  | abs {A A' b b'} : KEq Γ A A' → KEq Γ b b' →
    KEq Γ (.abs A b) (.abs A' b')
  | app {f f' a a'} : KEq Γ f f' → KEq Γ a a' → KEq Γ (.app f a) (.app f' a')
  | pair {a a' b b'} : KEq Γ a a' → KEq Γ b b' →
    KEq Γ (.pair a b) (.pair a' b')
  | fst {p p'} : KEq Γ p p' → KEq Γ (.fst p) (.fst p')
  | snd {p p'} : KEq Γ p p' → KEq Γ (.snd p) (.snd p')
  | dite {φ φ' l l' r r'} : KEq Γ φ φ' → KEq Γ l l' → KEq Γ r r' →
    KEq Γ (.dite φ l r) (.dite φ' l' r')
  | trunc {A A'} : KEq Γ A A' → KEq Γ (.trunc A) (.trunc A')
  | choose {A A' φ φ'} : KEq Γ A A' → KEq Γ φ φ' → KEq Γ (.choose A φ) (.choose A' φ')
  | nats : KEq Γ .nats .nats
  | zero : KEq Γ .zero .zero
  | succ {n n'} : KEq Γ n n' → KEq Γ (.succ n) (.succ n')
  | natrec {C C' s  s' z  z' n n'} : KEq Γ C C' → KEq Γ s s' →
    KEq Γ z z' → KEq Γ n n' → KEq Γ (.natrec C s z n) (.natrec C' s' z' n')
  | has_ty {A A' a a'} : KEq Γ A A' → KEq Γ a a' → KEq Γ (.has_ty A a) (.has_ty A' a')
  | invalid : KEq Γ .invalid .invalid
  | wf_clamp {a b} : KWEq Γ a b → KEq Γ a b
  | trans {a b c} : KEq Γ a b → KEq Γ b c → KEq Γ a c

theorem Ctx.RwEq.erase {k} {Γ} {a b : Tm k} (h : RwEq Γ a b) : KEq Γ a.erase b.erase := by
  induction h with
  | wf_clamp h => apply KEq.wf_clamp; convert h; simp only [KWEq, Tm.erase_clamp]
  | trans => apply KEq.trans <;> assumption
  | _ => constructor <;> assumption

theorem Ctx.KEq.clamp {Γ} {a b : OTm} (h : KEq Γ a b) (k : ℕ) : RwEq Γ (a.clamp k) (b.clamp k) := by
  induction h generalizing k with
  | bv => apply RwEq.refl
  | wf_clamp h => apply RwEq.wf_clamp; convert h; simp [KWEq]
  | trans => apply RwEq.trans <;> apply_assumption
  | _ => constructor <;> apply_assumption

theorem Ctx.KEq.clamp_iff {Γ} {a b : OTm} : KEq Γ a b ↔ ∀ k, RwEq Γ (a.clamp k) (b.clamp k) := ⟨
  fun h => h.clamp,
  fun h => by convert (h (a.bvi ⊔ b.bvi)).erase <;> rw [OTm.erase_clamp_bvi_le] <;> simp⟩

@[simp, refl]
theorem Ctx.KEq.refl {Γ} {a : OTm} : KEq Γ a a := by
  induction a with
  | bv => apply KEq.bv
  | _ => constructor <;> apply_assumption

theorem Ctx.KEq.of_eq {Γ} {a b : OTm} (h : a = b) : KEq Γ a b := by cases h; rfl

@[symm]
theorem Ctx.KEq.symm {Γ} {a b : OTm} (h : KEq Γ a b) : KEq Γ b a := by
  rw [clamp_iff] at *
  exact (fun k => (h k).symm)

theorem Ctx.KEq.psub {Γ Δ} (h : Γ.PSub Δ) {a b : OTm} (hab : KEq Δ a b) : KEq Γ a b := by
  rw [clamp_iff] at *
  exact (fun k => (hab k).psub h)

theorem Ctx.KEq.not_ok {Γ} (hΓ : ¬Ok Γ) {k} {a b : Tm k} (hab : RwEq Γ a b) : a = b
  := by induction hab with
  | wf_clamp h => exact (hΓ h.ok).elim
  | _ => simp only [*]

theorem Ctx.KEq.wk0
  {Γ} {k} {a b : Tm k} (hab : RwEq Γ a b) {x X} (hx : x ∉ Γ.dv) (hX : X ∈ RwTy Γ)
  : RwEq (Γ.cons x X) a b
  := open Classical in
  if hΓ : Ok Γ then
    hab.psub (hΓ.psub.skip hx (hX hΓ))
  else
    .of_eq (not_ok hΓ hab)

theorem Ctx.KEq.jeq {Γ} {A a b : OTm} (h : KEq Γ a b) (ha : KHasTy Γ A a)
  : KJEq Γ A a b := (h.clamp 0).lwreq.jeq_or (.inl ha)

theorem Ctx.KEq.has_ty_mp {Γ} {A a b : OTm} (h : KEq Γ a b)
  (ha : KHasTy Γ A a) : KHasTy Γ A b
  := (h.jeq ha).rhs_ty

theorem Ctx.KEq.has_ty_iff {Γ} {A a b : OTm} (h : KEq Γ a b)
  : KHasTy Γ A a ↔ KHasTy Γ A b
  := ⟨h.has_ty_mp, h.symm.has_ty_mp⟩

theorem Ctx.KEq.ty_eq {Γ} {A B : OTm} (h : KEq Γ A B) (hA : KIsTy Γ A)
  : KTyEq Γ A B := have ⟨ℓ, hA⟩ := hA; ⟨ℓ, (h.clamp 0).jeq hA.lhs_ty⟩

theorem Ctx.KEq.is_ty {Γ} {A B : OTm} (h : KEq Γ A B) (hA : KIsTy Γ A)
  : KIsTy Γ B := (h.ty_eq hA).rhs

theorem Ctx.KEq.is_ty_iff {Γ} {A B : OTm} (h : KEq Γ A B)
  : KIsTy Γ A ↔ KIsTy Γ B := ⟨h.is_ty, h.symm.is_ty⟩

theorem Ctx.KEq.weq {Γ} {a b : OTm} (h : KEq Γ a b) (ha : KIsWf Γ a)
  : KWEq Γ a b := (h.clamp 0).weq ha

theorem Ctx.KEq.is_wf {Γ} {a b : OTm} (h : KEq Γ a b) (hA : KIsWf Γ a)
  : KIsWf Γ b := (h.weq hA).rhs

theorem Ctx.KEq.wf_iff {Γ} {a b : OTm} (h : KEq Γ a b)
  : KIsWf Γ a ↔ KIsWf Γ b := ⟨h.is_wf, h.symm.is_wf⟩

theorem Ctx.KEq.lst {Γ} {a a' b b' : OTm} {k} (hb : KEq Γ b b') (ha : KEq Γ a a')
  : KEq Γ (b.lst k a) (b'.lst k a') := by induction hb generalizing k a with
  | wf_clamp h =>
    rw [OTm.lst_bvi, OTm.lst_bvi]
    · exact .wf_clamp h
    · rw [h.rhs.lc]; omega
    · rw [h.lhs.lc]; omega
  | trans _ _ Ia Ib => apply trans (Ia ha) (Ib .refl)
  | bv =>
    simp; split
    · rfl
    split
    · exact ha
    · rfl
  | _ => constructor <;> apply_assumption <;> assumption

theorem Ctx.KEq.open {Γ} {a b : OTm} (h : KEq Γ a b) (k x)
  : KEq Γ (a.open k x) (b.open k x)
  := by convert h.lst (.refl (a := .fv x)) using 1 <;> rw [OTm.lst_of_fv]

theorem Ctx.KEq.wkn {Γ} {a b : OTm} (h : KEq Γ a b) (k)
  : KEq Γ (a.wkn k) (b.wkn k)
  := by induction h generalizing k with
  | wf_clamp h =>
    rw [OTm.wkn_of_bvi_le, OTm.wkn_of_bvi_le]
    · exact .wf_clamp h
    · simp [h.rhs.lc]
    · simp [h.lhs.lc]
  | bv => rfl
  | trans => apply trans <;> apply_assumption
  | _ => constructor <;> apply_assumption

theorem Ctx.KEq.st {Γ} {a a' b b' : OTm} {k} (hb : KEq Γ b b') (ha : KEq Γ a a')
  : KEq Γ (b.st k a) (b'.st k a') := by induction hb generalizing k a a' with
  | wf_clamp h =>
    rw [OTm.st_bvi, OTm.st_bvi]
    · exact .wf_clamp h
    · rw [h.rhs.lc]; omega
    · rw [h.lhs.lc]; omega
  | trans _ _ Ia Ib => apply trans (Ia ha) (Ib .refl)
  | bv =>
    simp; split
    · rfl
    split
    · exact ha
    · rfl
  | _ =>  constructor <;> apply_assumption <;> (try apply wkn) <;> assumption

def Ctx.HasTyUnder (Γ : Ctx) (A : Tm 0) (B b : Tm 1) : Prop
  := ∀ x ∉ Γ.dv, HasTy (Γ.cons x A) (B.open x) (b.open x)

def Ctx.KHasTyUnder (Γ : Ctx) (A B b : OTm) : Prop
  := ∀ x ∉ Γ.dv, KHasTy (Γ.cons x (A.clamp 0)) (B.open 0 x) (b.open 0 x)

theorem Ctx.KHasTyUnder.get {Γ A B b} (h : KHasTyUnder Γ A B b)
  : HasTyUnder Γ (A.clamp 0) (B.clamp 1) (b.clamp 1)
  := by
  simp only [HasTyUnder]
  intro x hx
  convert (h x hx).get <;> simp [OTm.clamp_succ_open]

theorem Ctx.KHasTy.wk0 {Γ A a} (h : KHasTy Γ A a) {x X} (hx : x ∉ Γ.dv) (hX : X ∈ RwTy Γ)
  : KHasTy (Γ.cons x X) A a
  := HasTy.wk0 h hx (hX h.ok)

theorem Ctx.KHasTy.under {Γ A B b} (hB : KIsTy Γ A) (h : KHasTy Γ B b)
  : KHasTyUnder Γ A B b
  := by
  intro x hx
  apply KHasTy.wk0 _ hx (fun _ => hB)
  convert h <;> rw [OTm.open_bvi] <;> rw [KIsWf.lc]
  · apply KIsTy.wf; apply KHasTy.regular; assumption
  · apply KHasTy.is_wf; assumption

theorem Ctx.KHasTy.close {Γ x A B b} (h : KHasTy (Γ.cons x (A.clamp 0)) B b)
  : KHasTyUnder Γ A (B.close 0 x) (b.close 0 x)
  := by
  intro y hy
  simp [KHasTy] at *
  convert h.rename_top y hy using 1 <;> rw [OTm.clamp_lsv] <;> simp [OTm.clamp, OTm.bvi]

theorem Ctx.KIsWf.to_has_ty {Γ A a} (ha : KIsWf Γ (.has_ty A a)) : KHasTy Γ A a := ha.get.to_has_ty

theorem Ctx.KIsWf.to_has_ty_under {Γ A B b} (h : KIsWf Γ (.abs A (.has_ty B b)))
  : KHasTyUnder Γ A B b
  := by
  intro x hx
  apply IsWf.to_has_ty
  have ⟨_, h⟩ := h.get;
  have ⟨_, h⟩ := h.lhs_ty.inner_ty;
  cases h with
  | abs hA hB hb =>
    convert (HasTy.top_quant_exact hb x hx).is_wf
    simp [OTm.clamp, OTm.clamp_succ_open]

theorem Ctx.KHasTyUnder.param {Γ A B b} (h : KHasTyUnder Γ A B b) : KIsTy Γ A
  := have ⟨x, hx⟩ := Γ.dv.exists_notMem; (h x hx).ok.ty

theorem Ctx.KHasTy.m_has_ty_wf {Γ A a} (ha : KHasTy Γ A a) : KIsWf Γ (.has_ty A a)
  := ⟨_, ha.get.m_has_ty.refl⟩

theorem Ctx.KHasTy.wf_iff {Γ A a} : KIsWf Γ (.has_ty A a) ↔ KHasTy Γ A a
  := ⟨KIsWf.to_has_ty, fun h => (m_has_ty_wf h)⟩

def Ctx.IsWfUnder (Γ : Ctx) (A : Tm 0) (B : Tm 1) : Prop
  := ∀ x ∉ Γ.dv, IsWf (Γ.cons x A) (B.open x)

def Ctx.IsTyUnder (Γ : Ctx) (A : Tm 0) (B : Tm 1) : Prop
  := ∀ x ∉ Γ.dv, IsTy (Γ.cons x A) (B.open x)

def Ctx.KIsWfUnder (Γ : Ctx) (A B : OTm) : Prop
  := ∀ x ∉ Γ.dv, KIsWf (Γ.cons x (A.clamp 0)) (B.open 0 x)

theorem Ctx.KIsWfUnder.param {Γ A B} (h : KIsWfUnder Γ A B) : KIsTy Γ A
  := have ⟨x, hx⟩ := Γ.dv.exists_notMem; (h x hx).ok.ty

theorem Ctx.KIsWfUnder.param_lc {Γ A B} (h : KIsWfUnder Γ A B) : A.bvi = 0
  := h.param.lc

theorem Ctx.KIsWfUnder.bvi_open_helper {Γ A B} (h : KIsWfUnder Γ A B) (x) (hx : x ∉ Γ.dv)
  : (B.open 0 x).bvi = 0 := (h x hx).lc

theorem Ctx.KIsWfUnder.bvi {Γ A B} (h : KIsWfUnder Γ A B)
  : B.bvi ≤ 1 := by
  have ⟨x, hx⟩ := Γ.dv.exists_notMem
  have ho : (B.open 0 x).bvi = 0 := h.bvi_open_helper x hx
  exact OTm.bvi_of_open_le 0 B x (by simp [ho])

def Ctx.KIsTyUnder (Γ : Ctx) (A B : OTm) : Prop
  := ∀ x ∉ Γ.dv, KIsTy (Γ.cons x (A.clamp 0)) (B.open 0 x)

theorem Ctx.KIsTyUnder.get {Γ A B} (h : KIsTyUnder Γ A B)
  : IsTyUnder Γ (A.clamp 0) (B.clamp 1)
  := fun x hx => by convert (h x hx).get; simp [OTm.clamp_succ_open]

theorem Ctx.KIsTyUnder.param {Γ A B} (h : KIsTyUnder Γ A B) : KIsTy Γ A
  := have ⟨x, hx⟩ := Γ.dv.exists_notMem; (h x hx).ok.ty

theorem Ctx.KHasTyUnder.ty {Γ A B b} (h : KHasTyUnder Γ A B b) : KIsTyUnder Γ A B
  := fun x hx => (h x hx).regular

theorem Ctx.KIsTyUnder.wf {Γ A B} (h : KIsTyUnder Γ A B) : KIsWfUnder Γ A B
  := fun x hx => (h x hx).wf

theorem Ctx.KIsTyUnder.max_univ {Γ A B} (h : KIsTyUnder Γ A B) : ∃ ℓ, KHasTyUnder Γ A (.univ ℓ) B
  := by
  have ⟨ℓ, h⟩ := IsTy.max_univ' (fun x hx => h.get x hx)
  exists ℓ
  intro x hx
  convert h x hx
  simp [KHasTy, HasTy', JEq.refl_iff, OTm.clamp_succ_open, OTm.clamp]

theorem Ctx.KHasTyUnder.is_wf {Γ A B b} (h : KHasTyUnder Γ A B b) : KIsWfUnder Γ A b
  := fun x hx => (h x hx).is_wf

theorem Ctx.KHasTy.univ {Γ ℓ} (h : Ok Γ) : KHasTy Γ (.univ (ℓ + 1)) (.univ ℓ)
  := HasTy.univ h

theorem Ctx.KHasTy.empty {Γ ℓ} (h : Ok Γ) : KHasTy Γ (.univ ℓ) .empty
  := HasTy.empty h

theorem Ctx.KHasTy.unit {Γ ℓ} (h : Ok Γ) : KHasTy Γ (.univ ℓ) .unit
  := HasTy.unit h

theorem Ctx.KHasTy.nats {Γ} (h : Ok Γ) : KHasTy Γ (.univ 1) .nats
  := HasTy.nats h

theorem Ctx.KHasTy.pi {Γ A B ℓ}
  (hA : KHasTy Γ (.univ ℓ) A) (hB : KHasTyUnder Γ A (.univ ℓ) B)
  (hℓ : 1 ≤ ℓ) : KHasTy Γ (.univ ℓ) (.pi A B)
  := HasTy.pi
    hA (fun x hx => by convert (hB x hx).get; simp [OTm.clamp_succ_open])
    (le_refl ℓ) (le_refl ℓ) hℓ

theorem Ctx.KHasTy.abs {Γ A B b}
  (hB : KHasTyUnder Γ A B b) : KHasTy Γ (.pi A B) (.abs A b)
  := HasTy.abs (fun x hx => by convert (hB x hx).get <;> simp [OTm.clamp_succ_open])

theorem Ctx.KHasTy.app {Γ A B f a}
  (hA : KHasTy Γ (.pi A B) f) (hB : KHasTy Γ A a) : KHasTy Γ (B.lst 0 a) (.app f a)
  := by
  rw [KHasTy]
  convert HasTy.app_e hA hB
  simp
  rw [OTm.clamp_lst]
  exact hB.is_wf.lc

theorem Ctx.KHasTy.sigma {Γ A B ℓ}
  (hA : KHasTy Γ (.univ ℓ) A) (hB : KHasTyUnder Γ A (.univ ℓ) B)
  (hℓ : 1 ≤ ℓ) : KHasTy Γ (.univ ℓ) (.sigma A B)
  := HasTy.sigma
    hA (fun x hx => by convert (hB x hx).get; simp [OTm.clamp_succ_open])
    (le_refl ℓ) (le_refl ℓ) hℓ

theorem Ctx.KHasTy.pair {Γ A B a b}
  (hB : KIsTyUnder Γ A B) (ha : KHasTy Γ A a) (hb : KHasTy Γ (B.lst 0 a) b)
  : KHasTy Γ (.sigma A B) (.pair a b) :=
  have ⟨ℓ, hB⟩ := hB.max_univ
  HasTy.pair
    (fun x hx => by convert (hB x hx).get; simp [OTm.clamp_succ_open]) ha
    (by convert hb.get; simp [OTm.clamp_lst (h := ha.is_wf.lc)])

theorem Ctx.KHasTy.fst {Γ A B p} (hp : KHasTy Γ (.sigma A B) p) : KHasTy Γ A (.fst p) :=
  HasTy.fst hp

theorem Ctx.KHasTy.snd {Γ A B p} (hp : KHasTy Γ (.sigma A B) p)
  : KHasTy Γ (B.lst 0 (.fst p)) (.snd p)
  := by convert HasTy.snd hp; simp [KHasTy, OTm.clamp_lst (h := hp.fst.is_wf.lc), OTm.clamp]

def Ctx.KIsProp (Γ : Ctx) (φ : OTm) : Prop := KHasTy Γ (.univ 0) φ

theorem Ctx.KHasTy.dite {Γ φ A l r}
  (hφ : KIsProp Γ φ) (hA : KIsTy Γ A) (hl : KHasTyUnder Γ φ A l) (hr : KHasTyUnder Γ φ.not A r)
  : KHasTy Γ A (.dite φ l r) :=
  have ⟨_, hA'⟩ := hA.get.has_ty; .dite' hφ hA'
  (fun x hx => by
    have hAi := A.open_bvi 0 x (by simp [hA.lc]);
    convert (hl x hx).get <;> simp [OTm.clamp_succ_open, hAi]
  ) (fun x hx => by
    have hAi := A.open_bvi 0 x (by simp [hA.lc]);
    convert (hr x hx).get <;> simp [OTm.clamp_succ_open, hAi]
  )

theorem Ctx.KHasTy.trunc {Γ A} (hA : KIsTy Γ A) : KIsProp Γ (.trunc A)
  := have ⟨_, hA⟩ := hA.get.has_ty; HasTy.trunc hA

def Ctx.KIsInhab (Γ : Ctx) (A : OTm) : Prop := ∃ a, KHasTy Γ A a

theorem Ctx.KHasTy.inhab {Γ A a} (h : KHasTy Γ A a) : KIsInhab Γ A := ⟨a, h⟩

theorem Ctx.KIsInhab.get {Γ A} (h : KIsInhab Γ A) : IsInhab Γ (A.clamp 0) :=
  have ⟨_, ha⟩ := h; ha.get.inhab

theorem Ctx.KIsInhab.is_ty {Γ A} (h : KIsInhab Γ A) : KIsTy Γ A := have ⟨_, ha⟩ := h; ha.regular

theorem Ctx.KIsInhab.wf {Γ A} (h : KIsInhab Γ A) : KIsWf Γ A := h.is_ty.wf

def Ctx.KIsPropUnder (Γ : Ctx) (A φ : OTm) : Prop := KHasTyUnder Γ A (.univ 0) φ

theorem Ctx.KHasTy.choose {Γ A φ}
  (hA : KIsInhab Γ A) (hφ : KIsPropUnder Γ A φ)
  : KHasTy Γ A (.choose A φ) :=
  have ⟨_, hA'⟩ := hA.is_ty.has_ty;
  HasTy.choose' hA' hA.get (fun x hx => by convert (hφ x hx).get; simp [OTm.clamp_succ_open])

theorem Ctx.KHasTy.succ {Γ n} (hn : KHasTy Γ .nats n) : KHasTy Γ .nats (.succ n)
  := HasTy.succ hn

theorem Ctx.KHasTy.natrec {Γ C s z n}
  (hC : KIsTyUnder Γ .nats C)
  (hs : KHasTyUnder Γ .nats (.arr C (C.st 0 (.succ (.bv 0)))) s)
  (hz : KHasTy Γ (C.lst 0 .zero) z)
  (hn : KHasTy Γ .nats n) : KHasTy Γ (C.lst 0 n) (.natrec C s z n)
  := by
  have ⟨_, hC'⟩ := hC.max_univ
  apply HasTy.natrec (L := Γ.dv)
  · intro x hx; convert (hC' x hx).get; simp only [OTm.clamp_succ_open]
  · intro x hx; convert (hs x hx).get
    · rw [
        <-OTm.succArrow_zero, OTm.open_succArrow, OTm.clamp_arr, Tm.open_succArrow,
        OTm.clamp_succ_open, OTm.clamp_lst
      ]
      · simp [OTm.clamp]
      · simp [OTm.bvi]
      · exact hC'.is_wf.bvi
    · simp only [OTm.clamp_succ_open]
  · convert hz.get; rw [OTm.clamp_lst (h := by simp [OTm.bvi])]; simp [OTm.clamp]
  · exact hn.get
  · rw [OTm.clamp_lst (h := hn.is_wf.lc)]
    apply IsTy.lst_cf'
    · intro x hx; convert (hC x hx).get; simp only [OTm.clamp_succ_open]
    · exact hn.refl

theorem Ctx.KHasTy.lst {Γ A B a b}
  (hb : KHasTyUnder Γ A B b) (ha : KHasTy Γ A a)
  : KHasTy Γ (B.lst 0 a) (b.lst 0 a)
  := by
  simp only [KHasTy, OTm.clamp_lst (h := ha.is_wf.lc)]
  exact HasTy.lst (fun x hx => by convert (hb x hx).get <;> simp [OTm.clamp_succ_open]) ha

theorem Ctx.KHasTy.st {Γ A B a b}
  (hb : KHasTyUnder Γ A B b) (ha : KHasTy Γ A a)
  : KHasTy Γ (B.st 0 a) (b.st 0 a)
  := by convert ha.lst hb using 1 <;> rw [OTm.st_eq_lst (hv := ha.is_wf.lc)]
