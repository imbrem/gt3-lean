import Gt3.HasTy.Regular

-- theorem Ctx.HasTy.tlst1_k {Γ : Ctx} {A B : Tm 0} {b : Tm 1} {a a' : Tm 0}
--   (hb : HasTy Γ B (b.lst a)) (ha : JEq Γ A a a') : JEq Γ B (b.lst a) (b.lst a') := by
--   generalize hba : b.lst a = ba at hb
--   induction hb generalizing b with
--   | cast_level => apply JEq.cast_level; apply_assumption <;> assumption
--   | cast => apply JEq.cast <;> apply_assumption <;> assumption
--   | _ =>
--     cases b with
--     | bv i => cases i using Fin.cases with
--       | zero => sorry
--       | succ => sorry
--     | _ => sorry
