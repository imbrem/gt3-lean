import Gt3.SubTy.Basic
import Gt3.HasTy.Cmp
import Gt3.HasTy.Regular

-- theorem Ctx.HasTy.cmp_ty {Γ A B a} (hA : HasTy Γ A a) (hB : HasTy Γ B a) : CmpTy Γ A B := by
--   induction hA generalizing B with
--   | cast h _ I => exact .trans (.of_eq h.symm) (I hB)
--   | cast_level h I => convert I hB using 0; simp
--   | fv hΓ hA =>
--     have ⟨W, hB, hW⟩ := hB.factor₂;
--     apply CmpTy.trans _ (.of_sub hW)
--     cases hB with
--     | fv _ hB =>
--       cases hA.unique hB
--       simp [hW.lhs]
--   | app' hB hA hf ha hba IB IA If Ia =>
--     have ⟨W, hB, hW⟩ := hB.factor₂;
--     apply CmpTy.trans _ (.of_sub hW)
--     cases hB with
--     | app' hB' hA' hf' ha' hba' =>
--       have If' := If hf'
--       have Ia' := Ia ha'
--       simp only [CmpTy.left_univ_iff] at *
--       sorry
--   | abs => sorry
--   | _ =>
--     have ⟨W, hB, hW⟩ := hB.factor₂;
--     apply CmpTy.trans _ (.of_sub hW)
--     cases hB
--     simp [*] <;> apply HasTy.ok <;> assumption

-- theorem Ctx.JEq.cmp_of_common {Γ A B a b c} (hab : JEq Γ A a b) (hbc : JEq Γ B b c) : CmpTy Γ A B
--   := by induction hab generalizing B c with
--   | _ => sorry
