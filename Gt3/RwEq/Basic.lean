import Gt3.JEq.Basic
import Gt3.HasTy.Factor
import Gt3.Syntax.LstBar
import Gt3.Syntax.LcInd

namespace Gt3

theorem Ctx.HasTy.valid {Γ A a} (h : HasTy Γ A a) : Tm.Valid a := by
  induction h <;> simp [Tm.forall_cf_open_valid_iff] at * <;> simp [*]

theorem Ctx.IsWf.valid {Γ a} (h : IsWf Γ a) : Tm.Valid a := have ⟨_, h⟩ := h.has_ty; h.valid

theorem Ctx.WfEq.lhs_valid {Γ a b} (h : WfEq Γ a b) : Tm.Valid a := h.lhs.valid

theorem Ctx.WfEq.rhs_valid {Γ a b} (h : WfEq Γ a b) : Tm.Valid b := h.rhs.valid

def Ctx.RwTy (Γ : Ctx) : Set (Tm 0) := { X | Ok Γ → IsTy Γ X }

@[simp] theorem Ctx.nats_rw_ty (Γ : Ctx) : .nats ∈ Γ.RwTy := fun h => .nats h

theorem Ctx.RwTy.of_has_ty {Γ ℓ A} (h : HasTy Γ (.univ ℓ) A) : A ∈ RwTy Γ := fun _ => h.is_ty

theorem Ctx.RwTy.of_has_ty_jeq {Γ ℓ U A A'}
  (h : HasTy Γ (.univ ℓ) A')
  (h' : JEq Γ U A A') : A ∈ RwTy Γ := fun _ => (h'.rtr h).lhs_is_ty

theorem Ctx.RwTy.of_has_ty_not {Γ φ} (h : HasTy Γ (.univ 0) φ) : φ.not ∈ RwTy Γ
  := fun _ => h.not.is_ty

theorem Ctx.RwTy.of_has_ty_not_jeq {Γ U φ φ'}
  (h : HasTy Γ (.univ 0) φ')
  (h' : JEq Γ U φ φ') : φ.not ∈ RwTy Γ := fun _ => (h'.rtr h).not.lhs_is_ty

inductive Ctx.LRwEq : Ctx → Tm 0 → Tm 0 → Prop
  | fv {Γ} (x) : LRwEq Γ (.fv x) (.fv x)
  | univ {Γ} (ℓ) : LRwEq Γ (.univ ℓ) (.univ ℓ)
  | empty {Γ} : LRwEq Γ .empty .empty
  | unit {Γ} : LRwEq Γ .unit .unit
  | null {Γ} : LRwEq Γ .null .null
  | eqn {Γ} {a a' b b'}
    : LRwEq Γ a a' → LRwEq Γ b b' → LRwEq Γ (.eqn a b) (.eqn a' b')
  | pi {Γ} {A A' B B'} {L : Finset String}
    : LRwEq Γ A A'
    → (∀x ∉ L, ∀X ∈ RwTy Γ, ∀y ∉ L, LRwEq (Γ.cons x X) (B.open y) (B'.open y))
    → LRwEq Γ (.pi A B) (.pi A' B')
  | sigma {Γ} {A A' B B'} {L : Finset String}
    : LRwEq Γ A A'
    → (∀x ∉ L, ∀X ∈ RwTy Γ, ∀y ∉ L, LRwEq (Γ.cons x X) (B.open y) (B'.open y))
    → LRwEq Γ (.sigma A B) (.sigma A' B')
  | abs {Γ} {A A' b b'} {L : Finset String}
    : LRwEq Γ A A'
    → (∀x ∉ L, ∀X ∈ RwTy Γ, ∀y ∉ L, LRwEq (Γ.cons x X) (b.open y) (b'.open y))
    → LRwEq Γ (.abs A b) (.abs A' b')
  | app {Γ} {f f' a a'} : LRwEq Γ f f' → LRwEq Γ a a' → LRwEq Γ (.app f a) (.app f' a')
  | pair {Γ} {a a' b b'} : LRwEq Γ a a' → LRwEq Γ b b' →
    LRwEq Γ (.pair a b) (.pair a' b')
  | fst {Γ} {p p'} : LRwEq Γ p p' → LRwEq Γ (.fst p) (.fst p')
  | snd {Γ} {p p'} : LRwEq Γ p p' → LRwEq Γ (.snd p) (.snd p')
  | dite {Γ} {φ φ' l l' r r'} {L : Finset String}
    : LRwEq Γ φ φ'
    → (∀x ∉ L, ∀X ∈ RwTy Γ, ∀y ∉ L, LRwEq (Γ.cons x X) (l.open y) (l'.open y))
    → (∀x ∉ L, ∀X ∈ RwTy Γ, ∀y ∉ L, LRwEq (Γ.cons x X) (r.open y) (r'.open y))
    → LRwEq Γ (.dite φ l r) (.dite φ' l' r')
  | trunc {Γ} {A A'} : LRwEq Γ A A' → LRwEq Γ (.trunc A) (.trunc A')
  | choose {Γ} {A A' φ φ'} {L : Finset String}
    : LRwEq Γ A A'
    → (∀x ∉ L, ∀X ∈ RwTy Γ, ∀y ∉ L, LRwEq (Γ.cons x X) (φ.open y) (φ'.open y))
    → LRwEq Γ (.choose A φ) (.choose A' φ')
  | nats {Γ} : LRwEq Γ .nats .nats
  | zero {Γ} : LRwEq Γ .zero .zero
  | succ {Γ} {n n'} : LRwEq Γ n n' → LRwEq Γ (.succ n) (.succ n')
  | natrec {Γ} {C C' s  s' z  z' n n'} {L : Finset String}
    : (∀x ∉ L, ∀X ∈ RwTy Γ, ∀y ∉ L, LRwEq (Γ.cons x X) (C.open y) (C'.open y))
    →  (∀x ∉ L, ∀X ∈ RwTy Γ, ∀y ∉ L, LRwEq (Γ.cons x X) (s.open y) (s'.open y))
    → LRwEq Γ z z' → LRwEq Γ n n' → LRwEq Γ (.natrec C s z n) (.natrec C' s' z' n')
  | has_ty {Γ} {A A' a a'} : LRwEq Γ A A' → LRwEq Γ a a' → LRwEq Γ (.has_ty A a) (.has_ty A' a')
  | invalid {Γ} : LRwEq Γ .invalid .invalid
  | wf {Γ} {a b} : WfEq Γ a b → LRwEq Γ a b
  | trans {Γ} {a b c} : LRwEq Γ a b → LRwEq Γ b c → LRwEq Γ a c

theorem Ctx.LRwEq.jeq_or {Γ} {A a b : Tm 0} (h : LRwEq Γ a b) (hab : HasTy Γ A a ∨ HasTy Γ A b)
  : JEq Γ A a b
  := by induction h generalizing A with
  | wf h => exact hab.elim h.ltr h.rtr
  | trans _ _ Iac Icb =>
    cases hab with
    | inl ha => have Iab := Iac (.inl ha); exact Iab.trans (Icb (.inl Iab.rhs_ty))
    | inr hb => have Icb := Icb (.inr hb); exact (Iac (.inr Icb.lhs_ty)).trans Icb
  | _ =>
    cases hab with
    | inl ha =>
      have ⟨W, hai⟩ := ha.inner_ty;
      apply JEq.ltr (A := W) _ ha
      try rename Finset String => L
      cases hai <;> {
        jeq_congr_f <;> first
        | {
          rename Finset String => K
          intros x hx
          have ⟨hxK, hxL⟩ : x ∉ K ∧ x ∉ L := by rw [<-Finset.notMem_union]; exact hx
          apply HasTy.refl; apply_assumption; assumption
        }
        | intros; apply HasTy.refl <;> apply_assumption <;> assumption
        | apply_assumption <;> apply Or.inl <;> assumption
        | {
          rename Finset String => K
          intros x hx
          have ⟨hxK, hxL⟩ : x ∉ K ∧ x ∉ L := by rw [<-Finset.notMem_union]; exact hx
          apply_assumption <;> first
          | assumption
          | apply RwTy.of_has_ty;
            (try apply HasTy.not) ; assumption | apply Or.inl; apply_assumption; exact hxK
          | simp
        }
      }
    | inr hb =>
      have ⟨W, hbi⟩ := hb.inner_ty;
      apply JEq.rtr (A := W) _ hb
      try rename Finset String => L
      cases hbi <;> {
        apply JEq.symm
        jeq_congr_f <;> first
        | {
          rename Finset String => K
          intros x hx
          have ⟨hxK, hxL⟩ : x ∉ K ∧ x ∉ L := by rw [<-Finset.notMem_union]; exact hx
          apply HasTy.refl; apply_assumption; assumption
        }
        | intros; apply HasTy.refl <;> apply_assumption <;> assumption
        | assumption
        | apply JEq.symm; apply_assumption ; apply Or.inr ; assumption
        | {
          rename Finset String => K
          intro x hx
          have ⟨hxK, hxL⟩ : x ∉ K ∧ x ∉ L := by rw [<-Finset.notMem_union]; exact hx
          apply JEq.symm
          apply_assumption <;> first
          | assumption
          | {
            first | apply RwTy.of_has_ty_not_jeq | apply RwTy.of_has_ty_jeq
            · assumption
            · apply JEq.rhs_ty'; apply_assumption; apply Or.inr; assumption
          } | {
            apply Or.inr;
            apply_assumption; exact hxK
          } | simp
        }
      }

theorem Ctx.LRwEq.jeq {Γ} {A a b : Tm 0} (h : LRwEq Γ a b) (ha : HasTy Γ A a)
  : JEq Γ A a b := h.jeq_or (.inl ha)

theorem Ctx.LRwEq.weq {Γ} {a b : Tm 0} (h : LRwEq Γ a b) (ha : IsWf Γ a)
  : WfEq Γ a b := have ⟨W, ha⟩ := ha.has_ty; ⟨W, h.jeq ha⟩

theorem Ctx.RwTy.psub {Γ Δ} (h : Γ.PSub Δ) {X} (hX : X ∈ RwTy Δ) : X ∈ RwTy Γ
  := fun _ => (hX h.right_ok).psub h

@[refl]
theorem Ctx.LRwEq.refl {Γ a} : LRwEq Γ a a
  := by induction a using Tm.lcIndCof ∅ generalizing Γ with
  | _ => constructor <;> first | exact ∅ | intros ; apply_assumption <;> simp

@[simp]
theorem Ctx.LRwEq.symm {Γ a b} (h : LRwEq Γ a b) : LRwEq Γ b a
  := by induction h with
  | wf h => exact wf h.symm
  | trans _ _ Ica Ibc => exact Ibc.trans Ica
  | _ => constructor <;> assumption

inductive Ctx.RwEq (Γ : Ctx) : ∀ {k}, Tm k → Tm k → Prop
  | fv (x) : RwEq Γ (.fv x) (.fv x)
  | bv (i) : RwEq Γ (.bv i) (.bv i)
  | univ (ℓ) : RwEq Γ (.univ ℓ) (.univ ℓ)
  | empty : RwEq Γ .empty .empty
  | unit : RwEq Γ .unit .unit
  | null : RwEq Γ .null .null
  | eqn {a a' b b'} : RwEq Γ a a' → RwEq Γ b b' → RwEq Γ (.eqn a b) (.eqn a' b')
  | pi {A A' B B'} : RwEq Γ A A' → RwEq Γ B B' → RwEq Γ (.pi A B) (.pi A' B')
  | sigma {A A' B B'} : RwEq Γ A A' → RwEq Γ B B' → RwEq Γ (.sigma A B) (.sigma A' B')
  | abs {A A' b b'} : RwEq Γ A A' → RwEq Γ b b' →
    RwEq Γ (.abs A b) (.abs A' b')
  | app {f f' a a'} : RwEq Γ f f' → RwEq Γ a a' → RwEq Γ (.app f a) (.app f' a')
  | pair {a a' b b'} : RwEq Γ a a' → RwEq Γ b b' →
    RwEq Γ (.pair a b) (.pair a' b')
  | fst {p p'} : RwEq Γ p p' → RwEq Γ (.fst p) (.fst p')
  | snd {p p'} : RwEq Γ p p' → RwEq Γ (.snd p) (.snd p')
  | dite {φ φ' l l' r r'} : RwEq Γ φ φ' → RwEq Γ l l' → RwEq Γ r r' →
    RwEq Γ (.dite φ l r) (.dite φ' l' r')
  | trunc {A A'} : RwEq Γ A A' → RwEq Γ (.trunc A) (.trunc A')
  | choose {A A' φ φ'} : RwEq Γ A A' → RwEq Γ φ φ' → RwEq Γ (.choose A φ) (.choose A' φ')
  | nats : RwEq Γ .nats .nats
  | zero : RwEq Γ .zero .zero
  | succ {n n'} : RwEq Γ n n' → RwEq Γ (.succ n) (.succ n')
  | natrec {C C' s  s' z  z' n n'} : RwEq Γ C C' → RwEq Γ s s' →
    RwEq Γ z z' → RwEq Γ n n' → RwEq Γ (.natrec C s z n) (.natrec C' s' z' n')
  | has_ty {A A' a a'} : RwEq Γ A A' → RwEq Γ a a' → RwEq Γ (.has_ty A a) (.has_ty A' a')
  | invalid : RwEq Γ .invalid .invalid
  | wf_clamp {a b} : WfEq Γ (a.clamp 0) (b.clamp 0) → RwEq Γ a b
  | trans {a b c} : RwEq Γ a b → RwEq Γ b c → RwEq Γ a c

theorem Ctx.RwEq.wf {Γ} {a b : Tm 0} (h : WfEq Γ a b) : RwEq Γ a b
  := by apply wf_clamp; convert h <;> simp

@[refl]
theorem Ctx.RwEq.refl {Γ} {k} (a : Tm k) : RwEq Γ a a
  := by induction a <;> constructor <;> assumption

theorem Ctx.RwEq.of_eq {Γ} {k} {a b : Tm k} (h : a = b) : RwEq Γ a b
  := h ▸ .refl a

@[symm]
theorem Ctx.RwEq.symm {Γ} {k} {a b : Tm k} (h : RwEq Γ a b) : RwEq Γ b a
  := by induction h with
  | wf_clamp h => exact .wf_clamp h.symm
  | trans _ _ Iab Ibc => exact .trans Ibc Iab
  | _ => constructor <;> assumption

theorem Ctx.RwEq.castLE {Γ} {lo hi} {a b : Tm lo} (h : lo ≤ hi) (hab : RwEq Γ a b)
  : RwEq Γ (a.castLE h) (b.castLE h)
  := by induction hab generalizing hi with
  | wf_clamp hw => apply wf_clamp; convert hw using 1 <;> simp
  | trans => apply trans <;> apply_assumption
  | _ => constructor <;> apply_assumption

theorem Ctx.RwEq.psub {Γ Δ} (h : Γ.PSub Δ) {k} {a b : Tm k} (hab : RwEq Δ a b) : RwEq Γ a b
  := by induction hab with
  | wf_clamp => apply wf_clamp; apply WfEq.psub h; assumption
  | trans => apply trans <;> assumption
  | _ => constructor <;> assumption

theorem Ctx.RwEq.not_ok {Γ} (hΓ : ¬Ok Γ) {k} {a b : Tm k} (hab : RwEq Γ a b) : a = b
  := by induction hab with
  | wf_clamp h => exact (hΓ h.ok).elim
  | _ => simp only [*]

theorem Ctx.RwEq.wk0
  {Γ} {k} {a b : Tm k} (hab : RwEq Γ a b) {x X} (hx : x ∉ Γ.dv) (hX : X ∈ RwTy Γ)
  : RwEq (Γ.cons x X) a b
  := open Classical in
  if hΓ : Ok Γ then
    hab.psub (hΓ.psub.skip hx (hX hΓ))
  else
    .of_eq (not_ok hΓ hab)

theorem Ctx.RwEq.lst_bar {Γ Δ} (h : PSub Γ Δ) {k} {a b : Tm k} {a' b'}
  (h : RwEq Δ a b) (h' : Tm.LstBar a b a' b') : LRwEq Γ a' b'
  := by induction h generalizing Γ a' b' with
  | wf_clamp hab =>
    apply LRwEq.wf (WfEq.psub h _)
    cases h'.lhs.clamp_valid hab.lhs_valid
    cases h'.rhs.clamp_valid hab.rhs_valid
    exact hab
  | fv => simp [h'.fv]; rfl
  | bv => simp [h'.bv]; rfl
  | univ => simp [h'.univ]; rfl
  | empty => simp [h'.empty]; rfl
  | unit => simp [h'.unit]; rfl
  | null => simp [h'.null]; rfl
  | eqn ha hb Ia Ib =>
    have _ := h'.eqn
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    constructor
    · apply Ia <;> assumption
    · apply Ib <;> assumption
  | pi hA hB IA IB =>
    have _ := h'.pi;
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    constructor
    · apply IA <;> assumption
    · {
      intro x hx X hX y hy
      apply IB
      · exact h.skip hx (hX h.left_ok)
      · apply Tm.LstBar.open; assumption
    }
  | abs hA hb IA Ib =>
    have _ := h'.abs;
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    constructor
    · apply IA <;> assumption
    · {
      intro x hx X hX y hy
      apply Ib
      · exact h.skip hx (hX h.left_ok)
      · apply Tm.LstBar.open; assumption
    }
  | sigma hA hB IA IB =>
    have _ := h'.sigma;
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    constructor
    · apply IA <;> assumption
    · {
      intro x hx X hX y hy
      apply IB
      · exact h.skip hx (hX h.left_ok)
      · apply Tm.LstBar.open; assumption
    }
  | app hf ha If Ia =>
    have _ := h'.app;
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    constructor
    · apply If <;> assumption
    · apply Ia <;> assumption
  | pair ha hb Ia Ib =>
    have _ := h'.pair;
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    constructor
    · apply Ia <;> assumption
    · apply Ib <;> assumption
  | fst hp Ip =>
    have _ := h'.fst;
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    constructor
    · apply Ip <;> assumption
  | snd hp Ip =>
    have _ := h'.snd;
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    constructor
    · apply Ip <;> assumption
  | dite hφ hl hr Iφ Il Ir =>
    have _ := h'.dite;
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    constructor
    · apply Iφ <;> assumption
    · {
      intro x hx X hX y hy
      apply Il
      · exact h.skip hx (hX h.left_ok)
      · apply Tm.LstBar.open; assumption
    }
    · {
      intro x hx X hX y hy
      apply Ir
      · exact h.skip hx (hX h.left_ok)
      · apply Tm.LstBar.open; assumption
    }
  | trunc hA IA =>
    have _ := h'.trunc;
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    constructor
    · apply IA <;> assumption
  | choose hA hφ IA Iφ =>
    have _ := h'.choose;
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    constructor
    · apply IA <;> assumption
    · {
      intro x hx X hX y hy
      apply Iφ
      · exact h.skip hx (hX h.left_ok)
      · apply Tm.LstBar.open; assumption
    }
  | nats => simp [h'.nats]; rfl
  | zero => simp [h'.zero]; rfl
  | succ hn In =>
    have _ := h'.succ;
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    constructor
    · apply In <;> assumption
  | natrec hC hs hz hn IC Is In Iz =>
    have _ := h'.natrec;
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    rename_i C s z n C' s' z' n' hC' hs' hz' hn'
    constructor
    · {
      intro x hx X hX y hy
      apply IC
      · exact h.skip hx (hX h.left_ok)
      · apply Tm.LstBar.open; assumption
    }
    · {
      intro x hx X hX y hy
      apply Is
      · exact h.skip hx (hX h.left_ok)
      · apply Tm.LstBar.open; assumption
    }
    --TODO: weird order...
    · apply In <;> assumption
    · apply Iz <;> assumption
  | has_ty hA ha IA Ia =>
    have _ := h'.has_ty;
    casesm* (∃_, _), (_ ∧ _), (_ = _)
    constructor
    · apply IA <;> assumption
    · apply Ia <;> assumption
  | invalid => simp [h'.invalid]; rfl
  | trans hac hcb Iac Icb =>
    rename_i a c b
    have ⟨c', hac', hcb'⟩ := h'.split c;
    apply LRwEq.trans
    · apply Iac h hac'
    · apply Icb h hcb'

theorem Ctx.RwEq.lwreq {Γ} {a b : Tm 0}
  (h : RwEq Γ a b) : LRwEq Γ a b
  := open Classical in by
  if hΓ : Ok Γ then
    exact h.lst_bar hΓ.psub .refl
  else
    cases h.not_ok hΓ; rfl

theorem Ctx.RwEq.jeq {Γ} {A a b : Tm 0} (h : RwEq Γ a b) (ha : HasTy Γ A a)
  : JEq Γ A a b := h.lwreq.jeq_or (.inl ha)

theorem Ctx.RwEq.has_ty_mp {Γ} {A a b : Tm 0} (h : RwEq Γ a b)
  (ha : HasTy Γ A a) : HasTy Γ A b
  := (h.jeq ha).rhs_ty

theorem Ctx.RwEq.has_ty_iff {Γ} {A a b : Tm 0} (h : RwEq Γ a b)
  : HasTy Γ A a ↔ HasTy Γ A b
  := ⟨h.has_ty_mp, h.symm.has_ty_mp⟩

theorem Ctx.RwEq.ty_eq {Γ} {A B : Tm 0} (h : RwEq Γ A B) (hA : IsTy Γ A)
  : TyEq Γ A B := have ⟨ℓ, hA⟩ := hA; ⟨ℓ, h.jeq hA.lhs_ty⟩

theorem Ctx.RwEq.is_ty {Γ} {A B : Tm 0} (h : RwEq Γ A B) (hA : IsTy Γ A)
  : IsTy Γ B := (h.ty_eq hA).rhs

theorem Ctx.RwEq.is_ty_iff {Γ} {A B : Tm 0} (h : RwEq Γ A B)
  : IsTy Γ A ↔ IsTy Γ B := ⟨h.is_ty, h.symm.is_ty⟩

theorem Ctx.RwEq.weq {Γ} {a b : Tm 0} (h : RwEq Γ a b) (ha : IsWf Γ a)
  : WfEq Γ a b := have ⟨W, ha⟩ := ha.has_ty; ⟨W, h.jeq ha⟩

theorem Ctx.RwEq.is_wf {Γ} {a b : Tm 0} (h : RwEq Γ a b) (hA : IsWf Γ a)
  : IsWf Γ b := (h.weq hA).rhs

theorem Ctx.RwEq.wf_iff {Γ} {a b : Tm 0} (h : RwEq Γ a b)
  : IsWf Γ a ↔ IsWf Γ b := ⟨h.is_wf, h.symm.is_wf⟩

end Gt3
