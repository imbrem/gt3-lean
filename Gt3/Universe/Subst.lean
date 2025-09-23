import Gt3.Universe.Level
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

@[simp]
def UExpr.uvs : UExpr -> Finset String
  | .uv u => {u}
  | .max a b => a.uvs ∪ b.uvs
  | .zero => ∅
  | .succ a => a.uvs

@[simp]
theorem UExpr.uvs_add (ℓ : UExpr) (n : ℕ) : (ℓ + n).uvs = ℓ.uvs := by
  induction n <;> simp [add_succ, *]

def UExpr.comp (u : String) : UExpr -> UExpr
  | .uv v => if u = v then 0 else .uv v
  | .max a b => .max (comp u a) (comp u b)
  | .zero => .zero
  | .succ a => .succ (comp u a)

theorem UExpr.comp_not_mem_uvs (u : String) (ℓ : UExpr) (h : u ∉ ℓ.uvs) : ℓ.comp u = ℓ := by
  induction ℓ with | _ => simp at h; simp [comp, *]

theorem UExpr.uvs_comp (u : String) (ℓ : UExpr) :
  (ℓ.comp u).uvs = ℓ.uvs.erase u := by
  induction ℓ with
  | uv v => simp only [comp]; split <;> simp [*]
  | _ => simp [comp, Finset.erase_union_distrib, *]

def UExpr.contrib (u : String) : UExpr -> UExpr
  | .uv v => if u = v then .uv u else 0
  | .max a b => .max (contrib u a) (contrib u b)
  | .zero => .zero
  | .succ a => .succ (contrib u a)

theorem UExpr.contrib_max_comp (u : String) (ℓ : UExpr) :
  (ℓ.contrib u).max (ℓ.comp u) ≈ ℓ := fun v => by
  induction ℓ with
  | uv v => simp only [comp, contrib]; split <;> simp [*]
  | _ => simp [comp, contrib] at * <;> omega

theorem UExpr.contrib_uvs (u : String) (ℓ : UExpr) :
  (ℓ.contrib u).uvs = {u} ∩ ℓ.uvs := by
  induction ℓ with
  | uv v => simp only [contrib]; split <;> simp [*]
  | _ => simp [contrib, Finset.inter_union_distrib_left, *]

@[simp]
def UExpr.evalOnly (u : String) (n : ℕ) : UExpr -> ℕ
  | .uv v => if u = v then n else 0
  | .max a b => (evalOnly u n a) ⊔ (evalOnly u n b)
  | .zero => 0
  | .succ a => (evalOnly u n a) + 1

@[simp]
def UExpr.multiplier (u : String) : UExpr -> ℕ
  | .uv v => if u = v then 1 else 0
  | .max a b => (multiplier u a) ⊔ (multiplier u b)
  | .zero => 0
  | .succ a => multiplier u a

@[simp]
def UExpr.offset (u : String) : UExpr -> ℕ
  | .uv _ => 0
  | .max a b => (multiplier u a * offset u a) ⊔ (multiplier u b * offset u b)
  | .zero => 0
  | .succ a => (multiplier u a * (offset u a + 1))

theorem UExpr.multiplier_zero_one (u : String) (a : UExpr)
  : (u ∉ a.uvs ∧ a.multiplier u = 0 ∧ a.offset u = 0) ∨ (u ∈ a.uvs ∧ a.multiplier u = 1) := by
  induction a with
  | uv v => simp only [multiplier]; split <;> simp [*]
  | _ => simp [multiplier] <;> grind

theorem UExpr.multiplier_one (u : String) (a : UExpr) (ha : u ∈ a.uvs) : a.multiplier u = 1 := by
  cases a.multiplier_zero_one u <;> simp [*] at *

theorem UExpr.multiplier_offset_zero (u : String) (a : UExpr) (ha : u ∉ a.uvs)
  : a.multiplier u = 0 ∧ a.offset u = 0 := by
  cases a.multiplier_zero_one u <;> simp [*] at *

@[simp]
theorem UExpr.multiplier_mul_multiplier (u : String) (a : UExpr) :
  (a.multiplier u) * (a.multiplier u) = a.multiplier u := by
  cases a.multiplier_zero_one u <;> simp [*]

@[simp]
theorem UExpr.multiplier_mul_offset (u : String) (a : UExpr) :
  (a.multiplier u) * (a.offset u) = a.offset u := by
  induction a with
  | uv v => simp only [multiplier, offset]; split <;> simp [*]
  | max a b ha hb => cases a.multiplier_zero_one u <;> cases b.multiplier_zero_one u <;> simp [*]
  | succ ℓ hℓ => simp [Nat.mul_add, *]
  | zero => simp

instance UValuation.instZero : Zero UValuation := ⟨fun _ => 0⟩

@[simp]
theorem UValuation.get_zero (u : String) : (0 : UValuation).get u = 0 := rfl

theorem UExpr.evalOnly_factor (u : String) (n : ℕ) (ℓ : UExpr) :
  ℓ.evalOnly u n = ((ℓ.multiplier u) * n + ℓ.offset u) ⊔ (ℓ.eval 0) := by
  induction ℓ with
  | max a b ha hb =>
    rw [evalOnly, ha, hb, eval, max_max_max_comm]
    cases a.multiplier_zero_one u <;> cases b.multiplier_zero_one u <;> simp [*]
  | succ ℓ hℓ => cases ℓ.multiplier_zero_one u <;> simp [*]; omega
  | _ => simp

def UValuation.set (v : UValuation) (u : String) (n : ℕ) : UValuation :=
  fun n' => if u = n' then n else v n'

@[simp]
theorem UValuation.get_set_self (v : UValuation) (u : String) (n : ℕ) :
  (v.set u n).get u = n := by simp [UValuation.set, UValuation.get]

theorem UExpr.eval_factor (v : UValuation) (ℓ : UExpr) (u : String) :
  ℓ.eval v = ((ℓ.multiplier u) * (v.get u) + ℓ.offset u) ⊔ (ℓ.eval (v.set u 0)) := by
  induction ℓ with
  | uv => simp [eval]; split <;> simp [UValuation.get, UValuation.set, *]
  | max a b ha hb =>
    rw [eval, ha, hb, eval, max_max_max_comm]
    cases a.multiplier_zero_one u <;> cases b.multiplier_zero_one u <;> simp [*]
  | succ ℓ hℓ => cases ℓ.multiplier_zero_one u <;> simp [*]; omega
  | _ => simp

instance UValuation.instOne : One UValuation := ⟨fun _ => 1⟩

@[simp] theorem UValuation.get_one (u : String) : (1 : UValuation).get u = 1 := rfl

def UValuation.only (u : String) (n : ℕ) : UValuation := (0 : UValuation).set u n

theorem UExpr.eval_only (u : String) (n : ℕ) (a : UExpr) :
  a.eval (UValuation.only u n) = a.evalOnly u n := by induction a with | uv => rfl | _ => simp [*]

theorem UExpr.eval_contrib_zero (u : String) (a : UExpr) :
  (a.contrib u).eval 0 = a.eval 0 := by induction a with
  | uv => simp only [contrib]; split <;> simp [*]
  | _ => simp [contrib, eval, *]

theorem UExpr.eval_comp_zero (u : String) (a : UExpr) :
  (a.comp u).eval 0 = a.eval 0 := by induction a with
  | uv v => simp only [comp]; split <;> simp [*]
  | _ => simp [comp, eval, *]

theorem UExpr.evalOnly_not_mem (u : String) (n : ℕ) (a : UExpr) (h : u ∉ a.uvs) :
  a.evalOnly u n = a.eval 0 := by induction a with | _ => simp at h; simp [evalOnly, *]

def UValuation.EqOn (us : Finset String) (v₁ v₂ : UValuation) : Prop
  := ∀ u ∈ us, v₁.get u = v₂.get u

theorem UValuation.EqOn.anti {us₁ us₂ : Finset String} {v₁ v₂ : UValuation}
  (h : v₁.EqOn us₂ v₂) (hsub : us₁ ⊆ us₂) : v₁.EqOn us₁ v₂ := fun u hu => h u (hsub hu)

theorem UExpr.eval_eqOn_subset
  (us : Finset String) {v₁ v₂ : UValuation} (h : v₁.EqOn us v₂) (a : UExpr) (ha : a.uvs ⊆ us)
  : a.eval v₁ = a.eval v₂ := by
  induction a with
  | uv u => simp at ha; simp [h u ha]
  | max _ _ Ia Ib =>
    simp [Finset.union_subset_iff] at ha
    simp [Ia ha.1, Ib ha.2]
  | succ _ I => simp [I ha]
  | zero => rfl

theorem UExpr.eval_eqOn (a : UExpr) {v₁ v₂ : UValuation} (h : v₁.EqOn a.uvs v₂)
  : a.eval v₁ = a.eval v₂ := eval_eqOn_subset a.uvs h a (by simp)

theorem UExpr.evalOnly_le {a b : UExpr} (h : a ≤ b) (u : String) (n : ℕ) :
  a.evalOnly u n ≤ b.evalOnly u n := by rw [<-eval_only, <-eval_only]; apply h

theorem UExpr.uvs_subset_of_le {a b : UExpr} (h : a ≤ b) : a.uvs ⊆ b.uvs := by
  intro u ha
  by_contra hb
  have habf := fun n => le_trans  (le_of_eq (a.evalOnly_factor u n).symm)
                                  (le_trans (evalOnly_le h u n)
                                  (le_of_eq (b.evalOnly_factor u n)))
  simp [a.multiplier_one u ha, b.multiplier_offset_zero u hb] at habf
  have habfn := habf (eval 0 b + 1)
  omega

theorem UExpr.uvs_equiv {a b : UExpr} (h : a ≈ b) : a.uvs = b.uvs :=
  le_antisymm (a.uvs_subset_of_le (UExpr.le_of_equiv h))
              (b.uvs_subset_of_le (UExpr.le_of_equiv (Setoid.symm h)))

def ULevel.uvs (ℓ : ULevel) : Finset String :=
  Quotient.liftOn ℓ UExpr.uvs (fun _ _ h => UExpr.uvs_equiv h)

@[simp]
theorem ULevel.uvs_uv (u : String) : (ULevel.uv u).uvs = {u} := rfl

@[simp]
theorem ULevel.uvs_zero : (0 : ULevel).uvs = ∅ := rfl

@[simp]
theorem ULevel.uvs_succ (ℓ : ULevel) : (ℓ.succ).uvs = ℓ.uvs := by
  induction ℓ using Quotient.inductionOn; rfl

@[simp]
theorem ULevel.uvs_sup (a b : ULevel) : (a ⊔ b).uvs = a.uvs ∪ b.uvs := by
  induction a, b using Quotient.inductionOn₂; rfl

@[simp]
theorem ULevel.uvs_add (ℓ : ULevel) (n : ℕ) : (ℓ + n).uvs = ℓ.uvs := by
  induction n <;> simp [ULevel.add_succ, *]

def ULevel.Subst : Type := String → ULevel

def ULevel.Subst.mk (f : String → ULevel) : ULevel.Subst := f

def ULevel.Subst.get (s : ULevel.Subst) (u : String) : ULevel := s u

@[simp]
theorem ULevel.Subst.get_mk (f : String → ULevel) (u : String) : (ULevel.Subst.mk f).get u = f u
  := rfl

@[ext]
theorem ULevel.Subst.ext {s₁ s₂ : ULevel.Subst} (h : ∀ u, s₁.get u = s₂.get u) : s₁ = s₂ := funext h

@[simp]
def UExpr.subst (s : ULevel.Subst) : UExpr → ULevel
  | UExpr.uv n => s.get n
  | UExpr.max a b => (subst s a) ⊔ (subst s b)
  | UExpr.zero => 0
  | UExpr.succ a => (subst s a).succ

def UValuation.subst (s : ULevel.Subst) (v : UValuation) : UValuation := fun n => (s.get n).eval v

@[simp]
theorem UValuation.get_subst (s : ULevel.Subst) (v : UValuation) (n : String) :
  (v.subst s).get n = (s.get n).eval v := rfl

theorem UExpr.eval_subst (s : ULevel.Subst) (v : UValuation) (a : UExpr) :
  (subst s a).eval v = a.eval (v.subst s) := by induction a <;> simp [eval, *]

theorem UExpr.subst_le {s : ULevel.Subst} {a b : UExpr} (h : a ≤ b) : subst s a ≤ subst s b
  := ULevel.le_of_eval_le (fun v => by rw [eval_subst, eval_subst]; exact h (v.subst s))

theorem UExpr.subst_eq {s : ULevel.Subst} {a b : UExpr} (h : a ≈ b) : subst s a = subst s b :=
  le_antisymm (subst_le (UExpr.le_of_equiv h)) (subst_le (UExpr.le_of_equiv (Setoid.symm h)))

def ULevel.subst (s : ULevel.Subst) (ℓ : ULevel) : ULevel :=
  Quotient.liftOn ℓ (UExpr.subst s) (fun _ _ h => UExpr.subst_eq h)

instance ULevel.Subst.instZero : Zero ULevel.Subst where zero := mk (fun _ => 0)

instance ULevel.Subst.instOne : One ULevel.Subst where one := mk (fun u => .uv u)

def ULevel.Subst.EqOn (us : Finset String) (v₁ v₂ : ULevel.Subst) : Prop
  := ∀ u ∈ us, v₁.get u = v₂.get u

theorem ULevel.Subst.EqOn.anti {us₁ us₂ : Finset String} {v₁ v₂ : ULevel.Subst}
  (h : v₁.EqOn us₂ v₂) (hsub : us₁ ⊆ us₂) : v₁.EqOn us₁ v₂ := fun u hu => h u (hsub hu)

theorem UExpr.subst_eqOn_subset
  (us : Finset String) {v₁ v₂ : ULevel.Subst} (h : v₁.EqOn us v₂) (a : UExpr) (ha : a.uvs ⊆ us)
  : a.subst v₁ = a.subst v₂ := by
  induction a with
  | uv u => simp at ha; simp [h u ha]
  | max _ _ Ia Ib =>
    simp [Finset.union_subset_iff] at ha
    simp [Ia ha.1, Ib ha.2]
  | succ _ I => simp [I ha]
  | zero => rfl

theorem UExpr.subst_eqOn (a : UExpr) {v₁ v₂ : ULevel.Subst} (h : v₁.EqOn a.uvs v₂)
  : a.subst v₁ = a.subst v₂ := subst_eqOn_subset a.uvs h a (by simp)

theorem ULevel.subst_eqOn_subset
  (us : Finset String) {v₁ v₂ : ULevel.Subst} (h : v₁.EqOn us v₂) (ℓ : ULevel) (hℓ : ℓ.uvs ⊆ us)
  : ℓ.subst v₁ = ℓ.subst v₂ := by
  induction ℓ using Quotient.inductionOn; apply UExpr.subst_eqOn_subset us h _ hℓ

theorem ULevel.subst_eqOn (ℓ : ULevel) {v₁ v₂ : ULevel.Subst} (h : v₁.EqOn ℓ.uvs v₂)
  : ℓ.subst v₁ = ℓ.subst v₂ := subst_eqOn_subset ℓ.uvs h ℓ (by simp)

@[simp]
theorem ULevel.Subst.get_one (u : String) : (1 : ULevel.Subst).get u = ULevel.uv u := rfl

@[simp]
theorem UExpr.subst_one (a : UExpr) : a.subst 1 = a.q := by induction a <;> simp [*]

@[simp]
theorem ULevel.subst_one (ℓ : ULevel) : ℓ.subst 1 = ℓ := by
  induction ℓ using Quotient.inductionOn
  simp [subst]
