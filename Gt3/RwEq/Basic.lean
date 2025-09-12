import Gt3.JEq.Basic
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
    : NoInvalid A → NoInvalid B → NoInvalid a → NoInvalid b → NoInvalid (.pair A B a b)
  | fst {p} : NoInvalid p → NoInvalid (.fst p)
  | snd {p} : NoInvalid p → NoInvalid (.snd p)

-- theorem Ctx.JEq.no_invalid {Γ A a b} (h : JEq Γ A a b)
--   : a.NoInvalid ∧ b.NoInvalid := by
--   sorry

-- theorem Ctx.WfEq.no_invalid {Γ a b} (h : WfEq Γ a b) : a.NoInvalid ∧ b.NoInvalid
--   := have ⟨_, h⟩ := h; h.no_invalid

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
  | pair {A A' B B' a a' b b'} : RwEq Γ A A' → RwEq Γ B B' → RwEq Γ a a' → RwEq Γ b b' →
    RwEq Γ (.pair A B a b) (.pair A' B' a' b')
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
