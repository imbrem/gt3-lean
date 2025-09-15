import Gt3.Syntax.Basic

def Tm.wkn {k} (j : ℕ) : Tm k → Tm (k + 1)
  | .fv x => .fv x
  | .bv i => if i < j then .bv i.castSucc else .bv i.succ
  | .univ ℓ => .univ ℓ

-- def Tm.arr {k} (A B : Tm k) : Tm k := .pi A (↑₊B)

-- @[simp]
-- theorem Tm.open_arr {k} (A B : Tm (k + 1)) (x : String)
-- : (Tm.arr A B).open x = .arr (A.open x) (B.open x) := by
--   simp only [arr, open_pi]
--   rw [B.open_castSucc]
