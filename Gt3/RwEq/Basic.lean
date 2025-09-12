import Gt3.JEq.Basic
import Gt3.HasTy.Factor
import Gt3.Syntax.Erase

inductive Tm.NoInvalid : ∀ {k}, Tm k → Prop
  | fv (x) : NoInvalid (.fv x)
  | bv (i) : NoInvalid (.bv i)
  | univ (ℓ) : NoInvalid (.univ ℓ)
  | eqn {a b} : NoInvalid a → NoInvalid b → NoInvalid (.eqn a b)
  | pi {A B} : NoInvalid A → NoInvalid B → NoInvalid (.pi A B)
  | sigma {A B} : NoInvalid A → NoInvalid B → NoInvalid (.sigma A B)
  | empty : NoInvalid .empty
  | unit : NoInvalid .unit
  | abs {A B b} : NoInvalid A → NoInvalid B → NoInvalid b → NoInvalid (.abs A B b)
  | app {f a} : NoInvalid f → NoInvalid a → NoInvalid (.app f a)
  | pair {A B a b}
    : NoInvalid A → NoInvalid B → NoInvalid a → NoInvalid b → NoInvalid (.pair a b)
  | fst {p} : NoInvalid p → NoInvalid (.fst p)
  | snd {p} : NoInvalid p → NoInvalid (.snd p)

-- theorem Ctx.JEq.no_invalid {Γ A a b} (h : JEq Γ A a b)
--   : a.NoInvalid ∧ b.NoInvalid := by
--   sorry

-- theorem Ctx.WfEq.no_invalid {Γ a b} (h : WfEq Γ a b) : a.NoInvalid ∧ b.NoInvalid
--   := have ⟨_, h⟩ := h; h.no_invalid

def Ctx.RwTy (Γ : Ctx) : Set (Tm 0) := { X | Ok Γ → IsTy Γ X }

theorem Ctx.RwTy.of_has_ty {Γ ℓ A} (h : HasTy Γ (.univ ℓ) A) : A ∈ RwTy Γ := fun _ => h.is_ty

theorem Ctx.RwTy.of_has_ty_jeq {Γ ℓ U A A'}
  (h : HasTy Γ (.univ ℓ) A')
  (h' : JEq Γ U A A') : A ∈ RwTy Γ := fun _ => (h'.rtr h).lhs_is_ty

inductive Ctx.LRwEq : Ctx → Tm 0 → Tm 0 → Prop
  | fv {Γ} (x) : LRwEq Γ (.fv x) (.fv x)
  | univ {Γ} (ℓ) : LRwEq Γ (.univ ℓ) (.univ ℓ)
  | null {Γ} : LRwEq Γ .null .null
  | eqn {Γ} {a a' b b'}
    : LRwEq Γ a a' → LRwEq Γ b b' → LRwEq Γ (.eqn a b) (.eqn a' b')
  | pi {Γ} {A A' B B'} {L : Finset String}
    : LRwEq Γ A A'
    → (∀x ∉ L, ∀X ∈ RwTy Γ, LRwEq (Γ.cons x X) (B.open x) (B'.open x))
    → LRwEq Γ (.pi A B) (.pi A' B')
  | sigma {Γ} {A A' B B'} {L : Finset String}
    : LRwEq Γ A A'
    → (∀x ∉ L, ∀X ∈ RwTy Γ, LRwEq (Γ.cons x X) (B.open x) (B'.open x))
    → LRwEq Γ (.sigma A B) (.sigma A' B')
  | empty {Γ} : LRwEq Γ .empty .empty
  | unit {Γ} : LRwEq Γ .unit .unit
  | abs {Γ} {A A' B B' b b'} {L : Finset String}
    : LRwEq Γ A A' → (∀x ∉ L, ∀X ∈ RwTy Γ, LRwEq (Γ.cons x X) (B.open x) (B'.open x))
    → (∀x ∉ L, ∀X ∈ RwTy Γ, LRwEq (Γ.cons x X) (b.open x) (b'.open x))
    → LRwEq Γ (.abs A B b) (.abs A' B' b')
  | app {Γ} {f f' a a'} : LRwEq Γ f f' → LRwEq Γ a a' → LRwEq Γ (.app f a) (.app f' a')
  | pair {Γ} {a a' b b'} {L : Finset String} : LRwEq Γ a a' → LRwEq Γ b b' →
    LRwEq Γ (.pair a b) (.pair a' b')
  | fst {Γ} {p p'} : LRwEq Γ p p' → LRwEq Γ (.fst p) (.fst p')
  | snd {Γ} {p p'} : LRwEq Γ p p' → LRwEq Γ (.snd p) (.snd p')
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
        | intros; apply HasTy.refl <;> apply_assumption <;> assumption
        | apply_assumption <;> apply Or.inl <;> assumption
        | {
          rename Finset String => K
          intros x hx
          have ⟨hxK, hxL⟩ : x ∉ K ∧ x ∉ L := by rw [<-Finset.notMem_union]; exact hx
          apply_assumption
          · exact hxL
          · apply RwTy.of_has_ty; assumption
          · apply Or.inl; apply_assumption; exact hxK
        }
      }
    | inr hb =>
      have ⟨W, hbi⟩ := hb.inner_ty;
      apply JEq.rtr (A := W) _ hb
      try rename Finset String => L
      cases hbi <;> {
        apply JEq.symm
        jeq_congr_f <;> first
        | intros; apply HasTy.refl <;> apply_assumption <;> assumption
        | assumption
        | apply JEq.symm; apply_assumption ; apply Or.inr ; assumption
        | {
          rename Finset String => K
          intro x hx
          have ⟨hxK, hxL⟩ : x ∉ K ∧ x ∉ L := by rw [<-Finset.notMem_union]; exact hx
          apply JEq.symm
          apply_assumption
          · exact hxL
          · apply RwTy.of_has_ty_jeq
            · assumption
            · apply JEq.rhs_ty'; apply_assumption; apply Or.inr; assumption
          · apply Or.inr;
            apply_assumption; exact hxK
        }
      }

theorem Ctx.LRwEq.jeq {Γ} {A a b : Tm 0} (h : LRwEq Γ a b) (ha : HasTy Γ A a)
  : JEq Γ A a b := h.jeq_or (.inl ha)

theorem Ctx.LRwEq.weq {Γ} {a b : Tm 0} (h : LRwEq Γ a b) (ha : IsWf Γ a)
  : WfEq Γ a b := have ⟨W, ha⟩ := ha.has_ty; ⟨W, h.jeq ha⟩

inductive Ctx.RwEq (Γ : Ctx) : ∀ {k}, Tm k → Tm k → Prop
  | fv (x) : RwEq Γ (.fv x) (.fv x)
  | bv (i) : RwEq Γ (.bv i) (.bv i)
  | univ (ℓ) : RwEq Γ (.univ ℓ) (.univ ℓ)
  | null : RwEq Γ .null .null
  | eqn {a a' b b'} : RwEq Γ a a' → RwEq Γ b b' → RwEq Γ (.eqn a b) (.eqn a' b')
  | pi {A A' B B'} : RwEq Γ A A' → RwEq Γ B B' → RwEq Γ (.pi A B) (.pi A' B')
  | sigma {A A' B B'} : RwEq Γ A A' → RwEq Γ B B' → RwEq Γ (.sigma A B) (.sigma A' B')
  | empty : RwEq Γ .empty .empty
  | unit : RwEq Γ .unit .unit
  | abs {A A' B B' b b'} : RwEq Γ A A' → RwEq Γ B B' → RwEq Γ b b' →
    RwEq Γ (.abs A B b) (.abs A' B' b')
  | app {f f' a a'} : RwEq Γ f f' → RwEq Γ a a' → RwEq Γ (.app f a) (.app f' a')
  | pair {a a' b b'} : RwEq Γ a a' → RwEq Γ b b' →
    RwEq Γ (.pair a b) (.pair a' b')
  | fst {p p'} : RwEq Γ p p' → RwEq Γ (.fst p) (.fst p')
  | snd {p p'} : RwEq Γ p p' → RwEq Γ (.snd p) (.snd p')
  | invalid : RwEq Γ .invalid .invalid
  | wf_clamp {a b} : WfEq Γ (a.erase.clamp 0) (b.erase.clamp 0) → RwEq Γ a b
  | trans {a b c} : RwEq Γ a b → RwEq Γ b c → RwEq Γ a c

theorem Ctx.RwEq.wf {Γ} {a b : Tm 0} (h : WfEq Γ a b) : RwEq Γ a b
  := by apply wf_clamp; convert h <;> simp

theorem Ctx.RwEq.refl {Γ} {k} (a : Tm k) : RwEq Γ a a
  := by induction a <;> constructor <;> assumption

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

-- theorem Ctx.RwEq.toJEq {Γ} {A a b : Tm 0} (h : RwEq Γ a b) (ha : HasTy Γ A a)
--   : JEq Γ A a b
--   := by
--   generalize hu : a = u
--   induction u using Tm.lcIndCof Γ.dv generalizing b with
--   | invalid => cases hu; cases ha.no_invalid.left
--   | _ =>
--     induction h with
--     | wf_clamp h => cases hu; apply WfEq.transfer _ ha; convert h <;> simp
--     | _ => first | assumption | fail

-- theorem Ctx.RwEq.toWf {Γ} {a b : Tm 0} (h : RwEq Γ a b) (ha : IsWf Γ a)
--   : WfEq Γ a b
--   := by induction a using Tm.lcIndCof Γ.dv generalizing b with
--   | _ =>
--     cases h with
--     | wf_clamp h => convert h <;> simp
--     | _ => sorry

-- inductive Ctx.ORwEq (Γ : Ctx) : OTm → OTm → Prop
--   | fv (x) : ORwEq Γ (.fv x) (.fv x)
--   | bv (i) : ORwEq Γ (.bv i) (.bv i)
--   | univ (ℓ) : ORwEq Γ (.univ ℓ) (.univ ℓ)
--   | null : ORwEq Γ .null .null
--   | eqn {a a' b b'} : ORwEq Γ a a' → ORwEq Γ b b' → ORwEq Γ (.eqn a b) (.eqn a' b')
--   | pi {A A' B B'} : ORwEq Γ A A' → ORwEq Γ B B' → ORwEq Γ (.pi A B) (.pi A' B')
--   | sigma {A A' B B'} : ORwEq Γ A A' → ORwEq Γ B B' → ORwEq Γ (.sigma A B) (.sigma A' B')
--   | empty : ORwEq Γ .empty .empty
--   | unit : ORwEq Γ .unit .unit
--   | abs {A A' B B' b b'} : ORwEq Γ A A' → ORwEq Γ B B' → ORwEq Γ b b' →
--     ORwEq Γ (.abs A B b) (.abs A' B' b')
--   | app {f f' a a'} : ORwEq Γ f f' → ORwEq Γ a a' → ORwEq Γ (.app f a) (.app f' a')
--   | pair {A A' B B' a a' b b'} : ORwEq Γ A A' → ORwEq Γ B B' → ORwEq Γ a a' → ORwEq Γ b b' →
--     ORwEq Γ (.pair A B a b) (.pair A' B' a' b')
--   | fst {p p'} : ORwEq Γ p p' → ORwEq Γ (.fst p) (.fst p')
--   | snd {p p'} : ORwEq Γ p p' → ORwEq Γ (.snd p) (.snd p')
--   | invalid : ORwEq Γ .invalid .invalid
--   | wf {a b} : WfEq Γ (a.clamp 0) (b.clamp 0) → ORwEq Γ a b
--   | trans {a b c} : ORwEq Γ a b → ORwEq Γ b c → ORwEq Γ a c

-- theorem Ctx.ORwEq.refl {Γ} (a) : ORwEq Γ a a := by induction a <;> constructor <;> assumption

-- theorem Ctx.ORwEq.symm {Γ} {a b} (h : ORwEq Γ a b) : ORwEq Γ b a
--   := by induction h with
--   | wf h => exact .wf h.symm
--   | trans _ _ Iab Ibc => exact .trans Ibc Iab
--   | _ => constructor <;> assumption

-- inductive Ctx.HRwEq (Γ : Ctx) : ∀ {kl kr}, Tm kl → Tm kr → Prop
--   | fv (x) : HRwEq Γ (.fv x) (.fv x)
--   | bv (il ir) : il.val = ir.val → HRwEq Γ (.bv il) (.bv ir)
--   | univ (ℓ) : HRwEq Γ (.univ ℓ) (.univ ℓ)
--   | null : HRwEq Γ .null .null
--   | eqn {a a' b b'} : HRwEq Γ a a' → HRwEq Γ b b' → HRwEq Γ (.eqn a b) (.eqn a' b')
--   | pi {A A' B B'} : HRwEq Γ A A' → HRwEq Γ B B' → HRwEq Γ (.pi A B) (.pi A' B')
--   | sigma {A A' B B'} : HRwEq Γ A A' → HRwEq Γ B B' → HRwEq Γ (.sigma A B) (.sigma A' B')
--   | empty : HRwEq Γ .empty .empty
--   | unit : HRwEq Γ .unit .unit
--   | abs {A A' B B' b b'} : HRwEq Γ A A' → HRwEq Γ B B' → HRwEq Γ b b' →
--     HRwEq Γ (.abs A B b) (.abs A' B' b')
--   | app {f f' a a'} : HRwEq Γ f f' → HRwEq Γ a a' → HRwEq Γ (.app f a) (.app f' a')
--   | pair {A A' B B' a a' b b'} : HRwEq Γ A A' → HRwEq Γ B B' → HRwEq Γ a a' → HRwEq Γ b b' →
--     HRwEq Γ (.pair A B a b) (.pair A' B' a' b')
--   | fst {p p'} : HRwEq Γ p p' → HRwEq Γ (.fst p) (.fst p')
--   | snd {p p'} : HRwEq Γ p p' → HRwEq Γ (.snd p) (.snd p')
--   | invalid : HRwEq Γ .invalid .invalid
--   | wf {a b} : WfEq Γ a b → HRwEq Γ a b
--   | trans {a b c} : HRwEq Γ a b → HRwEq Γ b c → HRwEq Γ a c

-- theorem Ctx.HRwEq.refl_cast {Γ} {lo hi : ℕ}
--   (h : lo ≤ hi) (t : Tm lo) : HRwEq Γ t (t.castLE h) := by
--   induction t generalizing hi <;> constructor <;> simp [*]

-- theorem Ctx.HRwEq.refl {Γ} {k : ℕ} (t : Tm k) : HRwEq Γ t t
--   := by convert HRwEq.refl_cast (le_refl _) t; simp

-- theorem Ctx.HRwEq.symm {Γ} {kl kr} {a : Tm kl} {b : Tm kr} (h : HRwEq Γ a b) : HRwEq Γ b a
--   := by induction h with
--   | wf h => exact .wf h.symm
--   | trans _ _ Iab Ibc => exact .trans Ibc Iab
--   | _ => constructor <;> simp [*]
