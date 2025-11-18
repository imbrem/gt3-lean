import Gt3.JEq.Basic

inductive Tel : ℕ → Type where
  | nil {n} : Tel n
  | cons {n} (A : Tm n) (Δ: Tel (n + 1)) : Tel n

def Tel.open {n} (Δ : Tel (n + 1)) (x : String) : Tel n := match Δ with
  | .nil => .nil
  | .cons A Δ => .cons (A.open x) (Δ.open x)

def Tel.lst {n} (Δ : Tel (n + 1)) (a : Tm 0) : Tel n := match Δ with
  | .nil => .nil
  | .cons A Δ => .cons (A.lst a) (Δ.lst a)

def Tel.length {n} : Tel n → ℕ
  | .nil => 0
  | .cons _ Δ => Δ.length + 1

structure CtxTel (n : ℕ) where
  ctx : Ctx
  tel : Tel n

inductive CtxTel.Ok : ∀ {n}, CtxTel n → Prop
  | base {Γ} : Γ.Ok → Ok ⟨Γ, .nil⟩
  | cons {Γ A Δ} {L : Finset String} (h : ∀ x ∉ L , Ok ⟨Γ.cons x A, Δ.open x⟩) : Ok ⟨Γ, .cons A Δ⟩

inductive CtxTel.JEq : ∀ {n}, CtxTel n → Tm n → Tm n → Tm n → Prop
  | base {Γ A a b} : Γ.JEq A a b → JEq ⟨Γ, .nil⟩ A a b
  | cons {Γ A Δ B a b} {L : Finset String}
    (h : ∀ x ∉ L , JEq ⟨Γ.cons x A, Δ.open x⟩ B a b)
    : JEq ⟨Γ, .cons A Δ⟩ B a b

--TODO: do with formula...

inductive CtxTel.WfEq : ∀ {n}, CtxTel n → Tm n → Tm n → Prop
  | base {Γ a b} : Γ.WfEq a b → WfEq ⟨Γ, .nil⟩ a b
  | cons {Γ A Δ a b} {L : Finset String}
    (h : ∀ x ∉ L , WfEq ⟨Γ.cons x A, Δ.open x⟩ a b)
    : WfEq ⟨Γ, .cons A Δ⟩ a b

-- theorem CtxTel.WfEq.jeq {n} {Γ : CtxTel n} {a : Tm n} {b : Tm n} (h : WfEq Γ a b)
--   : ∃ A , JEq Γ A a b
--   := by induction h with
--   | base h => have ⟨A, h⟩ := h; exact ⟨A, .base h⟩
--   | cons h I =>
--     rename Finset String => L
--     rename_i a b
--     have ⟨x, hx⟩ := L.exists_notMem;
--     have ⟨A, hA⟩ := I x hx
--     exact ⟨A, .cons (L := L) (fun x hx => sorry)⟩
