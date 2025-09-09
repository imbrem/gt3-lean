import Gt3.HasTy.Subst

def Ctx.Cmp (Γ : Ctx) (A a b : Tm 0) : Prop := HasTy Γ A a ∧ HasTy Γ A b

theorem Ctx.Cmp.cast_level {Γ ℓ A B} (h : Cmp Γ (.univ ℓ) A B) : Cmp Γ (.univ (ℓ + 1)) A B
  := ⟨h.left.cast_level, h.right.cast_level⟩

theorem Ctx.Cmp.cast' {Γ ℓ A A' a b} (hA : JEq Γ (.univ ℓ) A A') (hab : Cmp Γ A a b)
  : Cmp Γ A' a b := ⟨hab.left.cast' hA, hab.right.cast' hA⟩

theorem Ctx.Cmp.symm {Γ A a b} (h : Cmp Γ A a b) : Cmp Γ A b a
  := ⟨h.right, h.left⟩

theorem Ctx.Cmp.trans {Γ A a b c} (h : Cmp Γ A a b) (h' : Cmp Γ A b c) : Cmp Γ A a c
  := ⟨h.left, h'.right⟩

-- theorem Ctx.JEq.cmp {Γ A a b} (h : JEq Γ A a b) : Cmp Γ A a b := by induction h with
--   | nil_ok => sorry
--   | cons_ok => sorry
--   | cast_level => apply Cmp.cast_level; assumption
--   | cast' => apply Cmp.cast' <;> assumption
--   | symm => apply Cmp.symm; assumption
--   | trans => apply Cmp.trans <;> assumption
--   | pi =>
--     sorry
--   | abs =>
--     sorry
--   | app' => sorry
--   | beta_app => sorry
--   | _ =>
--     simp only [Ctx.Cmp, forall_and] at *
--     casesm* _ ∧ _
--     apply And.intro <;>
--     first
--     | assumption
--     | {
--         constructor <;> first
--         | assumption
--         | apply Ctx.JEq.ok ; assumption
--         | apply JEq.ty_eq ; assumption
--         -- | intros <;> apply HasTy.cast_top' <;> fail
--         -- | fail
--       }
