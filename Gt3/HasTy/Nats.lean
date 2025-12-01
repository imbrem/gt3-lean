import Gt3.HasTy.Basic

namespace Gt3

def Tm.ofNat {k} : ℕ → Tm k
  | 0 => .zero
  | n + 1 => .succ (.ofNat n)

instance {k n} : OfNat (Tm k) n where ofNat := Tm.ofNat n

theorem Tm.zero_def {k} : (0 : Tm k) = .zero := rfl

theorem Ctx.HasTy.nat (n : ℕ) {Γ} (hΓ : Ok Γ) : HasTy Γ .nats (Tm.ofNat n) := by
  induction n with | zero => exact zero hΓ | succ _ I => exact I.succ

theorem Ctx.JEq.nat (n : ℕ) {Γ} (hΓ : Ok Γ) : JEq Γ .nats (Tm.ofNat n) (Tm.ofNat n)
  := (HasTy.nat n hΓ).refl

instance {k} : Add (Tm k) where
  add a b := .natrec .nats (.succ (.bv 0)) a b

end Gt3
