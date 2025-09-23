import Gt3.Universe.Level
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

def UExpr.isZero : UExpr → Bool
  | .zero => true
  | .imax _ b => b.isZero
  | .max a b => a.isZero && b.isZero
  | _ => false

@[simp]
theorem UExpr.zero_eqv_zero' : (0 : UExpr) ≈ UExpr.zero := by intro v; rfl

@[simp]
theorem UExpr.zero'_eqv_zero : UExpr.zero ≈ (0 : UExpr) := by intro v; rfl

@[simp]
theorem UExpr.succ_not_eqv_zero (a : UExpr) : ¬ (a.succ ≈ 0) := by intro h; cases h (fun u => 0)

@[simp]
theorem UExpr.uv_not_eqv_zero (u : String) : ¬ (UExpr.uv u ≈ 0) := by intro h; cases h (fun u => 1)

theorem UExpr.isZero_iff {u : UExpr} : u.isZero ↔ u ≈ 0 := by
  induction u with
  | imax a b Ia Ib =>
    simp [isZero]
    convert Ib using 1
    apply forall_congr'
    intro v
    simp [Nat.imax]
    omega
  | max a b Ia Ib =>
    simp [isZero, *]
    constructor
    · intro h v; simp [h.1 v, h.2 v]
    · intro h; constructor <;> intro v <;> have hv := h v <;> simp at hv <;> simp [*]
  | _ => simp [isZero]

instance UExpr.decidableIsZero : DecidablePred (fun u : UExpr => u ≈ 0)
  := fun u => decidable_of_iff (u.isZero) UExpr.isZero_iff

@[simp]
theorem UExpr.imax_eqv_zero_iff {a b : UExpr} : (UExpr.imax a b ≈ 0) ↔ (b ≈ 0) := by
  simp [<-UExpr.isZero_iff, isZero]

@[simp]
theorem UExpr.max_eqv_zero_iff {a b : UExpr} : (UExpr.max a b ≈ 0) ↔ (a ≈ 0 ∧ b ≈ 0) := by
  simp [<-UExpr.isZero_iff, isZero]

@[simp]
theorem UExpr.eval_imax_zero {a b : UExpr} (hb : b ≈ 0) (v : UValuation) :
  (UExpr.imax a b).eval v = 0 := by simp [Nat.imax, hb v]

theorem UExpr.isZero_equiv {u : UExpr} (h : u.isZero) : u ≈ 0 := by
  induction u with
  | imax a b Ia Ib => intro v; simp [Ib h v, Nat.imax]
  | max a b Ia Ib => simp [isZero] at h; intro v; simp [Ia h.1 v, Ib h.2 v]
  | _ => simp [isZero] at h <;> intro v <;> rfl

@[simp]
def UExpr.uvs : UExpr -> Finset String
  | .uv u => {u}
  | .imax a b => if b ≈ 0 then ∅ else a.uvs ∪ b.uvs
  | .max a b => a.uvs ∪ b.uvs
  | .zero => ∅
  | .succ a => a.uvs

@[simp]
theorem UExpr.uvs_add (ℓ : UExpr) (n : ℕ) : (ℓ + n).uvs = ℓ.uvs := by
  induction n <;> simp [add_succ, *]

def UExpr.comp (u : String) : UExpr -> UExpr
  | .uv v => if u = v then 0 else .uv v
  | .imax a b => .imax (comp u a) (comp u b)
  | .max a b => .max (comp u a) (comp u b)
  | .zero => .zero
  | .succ a => .succ (comp u a)

def UExpr.contrib (u : String) : UExpr -> UExpr
  | .uv v => if u = v then .uv u else 0
  | .imax a b => .imax (contrib u a) (contrib u b)
  | .max a b => .max (contrib u a) (contrib u b)
  | .zero => .zero
  | .succ a => .succ (contrib u a)

@[simp]
def UExpr.evalOnly (u : String) (n : ℕ) : UExpr -> ℕ
  | .uv v => if u = v then n else 0
  | .imax a b => (evalOnly u n a).imax (evalOnly u n b)
  | .max a b => (evalOnly u n a) ⊔ (evalOnly u n b)
  | .zero => 0
  | .succ a => (evalOnly u n a) + 1

instance UValuation.instZero : Zero UValuation := ⟨fun _ => 0⟩

@[simp]
theorem UValuation.get_zero (u : String) : (0 : UValuation).get u = 0 := rfl

def UValuation.set (v : UValuation) (u : String) (n : ℕ) : UValuation :=
  fun n' => if u = n' then n else v n'

@[simp]
theorem UValuation.get_set_self (v : UValuation) (u : String) (n : ℕ) :
  (v.set u n).get u = n := by simp [UValuation.set, UValuation.get]

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

def UValuation.EqOn (us : Finset String) (v₁ v₂ : UValuation) : Prop
  := ∀ u ∈ us, v₁.get u = v₂.get u

theorem UValuation.EqOn.anti {us₁ us₂ : Finset String} {v₁ v₂ : UValuation}
  (h : v₁.EqOn us₂ v₂) (hsub : us₁ ⊆ us₂) : v₁.EqOn us₁ v₂ := fun u hu => h u (hsub hu)

theorem UExpr.eval_eqOn_subset
  (us : Finset String) {v₁ v₂ : UValuation} (h : v₁.EqOn us v₂) (a : UExpr) (ha : a.uvs ⊆ us)
  : a.eval v₁ = a.eval v₂ := by
  induction a with
  | uv u => simp at ha; simp [h u ha]
  | imax _ _ Ia Ib =>
    simp at ha
    split at ha
    case isTrue h => rw [UExpr.eval_imax_zero, UExpr.eval_imax_zero] <;> assumption
    case isFalse h =>
      simp [Finset.union_subset_iff] at ha
      simp [Ia ha.1, Ib ha.2]
  | max _ _ Ia Ib =>
    simp [Finset.union_subset_iff] at ha
    simp [Ia ha.1, Ib ha.2]
  | succ _ I => simp [I ha]
  | zero => rfl

theorem UExpr.eval_eqOn (a : UExpr) {v₁ v₂ : UValuation} (h : v₁.EqOn a.uvs v₂)
  : a.eval v₁ = a.eval v₂ := eval_eqOn_subset a.uvs h a (by simp)

theorem UExpr.evalOnly_le {a b : UExpr} (h : a ≤ b) (u : String) (n : ℕ) :
  a.evalOnly u n ≤ b.evalOnly u n := by rw [<-eval_only, <-eval_only]; apply h

@[simp]
def UExpr.evalOnly1 (u : String) (n : ℕ) : UExpr -> ℕ
  | .uv v => if u = v then n else 1
  | .imax a b => (evalOnly1 u n a).imax (evalOnly1 u n b)
  | .max a b => (evalOnly1 u n a) ⊔ (evalOnly1 u n b)
  | .zero => 0
  | .succ a => (evalOnly1 u n a) + 1

theorem UExpr.evalOnlyOne_zero_eq_zero {u : String} {ℓ : UExpr} {n}
  (hℓ : ℓ.evalOnly1 u (n + 1) = 0) : ℓ ≈ 0
  := by induction ℓ <;> simp [Nat.imax] at * <;> grind

theorem UExpr.nonempty_dvs_not_zero {u : String} {ℓ : UExpr}
  (hu : u ∈ ℓ.uvs) : ¬ (ℓ ≈ 0)
  := by induction ℓ <;> simp at * <;> (try split at hu) <;> grind

theorem UExpr.evalOnlyOne_nonempty_dvs {u : String} {ℓ : UExpr} {n}
  (hu : u ∈ ℓ.uvs) : ℓ.evalOnly1 u (n + 1) ≠ 0
  := fun h => nonempty_dvs_not_zero hu (evalOnlyOne_zero_eq_zero h)

theorem UExpr.evalOnly1_increasing {u : String} {ℓ : UExpr}
(hu : u ∈ ℓ.uvs) (n) : n ≤ ℓ.evalOnly1 u n
  := by induction ℓ with
  | imax a b Ia Ib =>
    simp at hu
    split at hu <;> simp at hu
    simp [Nat.imax]
    cases n with
    | zero => simp
    | succ n =>
      rw [ite_cond_eq_false]
      · simp; grind
      simp only [eq_iff_iff, iff_false]; intro h; have hb := evalOnlyOne_zero_eq_zero h
      contradiction
  | _ => simp; (try split) <;> simp at hu <;> grind

theorem UExpr.eval_set1 (u : String) (n : ℕ) (a : UExpr) :
  a.eval (UValuation.set 1 u n) = a.evalOnly1 u n := by induction a with | uv => rfl | _ => simp [*]

theorem UExpr.evalOnly1_mono_level {lo hi : UExpr}
  (h : lo ≤ hi) (u n) : lo.evalOnly1 u n ≤ hi.evalOnly1 u n
  := by rw [<-eval_set1, <-eval_set1]; apply h

theorem UExpr.evalOnly1_const_not_mem {u : String} (ℓ : UExpr)
  (hu : u ∉ ℓ.uvs) (n m) : ℓ.evalOnly1 u n = ℓ.evalOnly1 u m
  := by
    rw [<-eval_set1, <-eval_set1]; apply eval_eqOn; intro v h
    simp [UValuation.set, UValuation.get]
    split <;> simp [*] at *

theorem UExpr.uvs_subset_of_le {a b : UExpr} (h : a ≤ b) : a.uvs ⊆ b.uvs := by
  intro u ha
  by_contra hb
  have habm := evalOnly1_increasing ha (b.evalOnly1 u 1 + 1)
  have habr := evalOnly1_mono_level h u (b.evalOnly1 u 1 + 1)
  simp [evalOnly1_const_not_mem _ hb _ 1] at habr
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
  | UExpr.imax a b => (subst s a).imax (subst s b)
  | UExpr.max a b => (subst s a) ⊔ (subst s b)
  | UExpr.zero => 0
  | UExpr.succ a => (subst s a).succ

def UValuation.subst (s : ULevel.Subst) (v : UValuation) : UValuation := fun n => (s.get n).eval v

@[simp]
theorem UValuation.get_subst (s : ULevel.Subst) (v : UValuation) (n : String) :
  (v.subst s).get n = (s.get n).eval v := rfl

theorem UExpr.eval_subst (s : ULevel.Subst) (v : UValuation) (a : UExpr) :
  (subst s a).eval v = a.eval (v.subst s) := by induction a <;> simp [eval, *]

theorem UExpr.subst_mono {s : ULevel.Subst} {a b : UExpr} (h : a ≤ b) : subst s a ≤ subst s b
  := ULevel.le_of_eval_le (fun v => by rw [eval_subst, eval_subst]; exact h (v.subst s))

theorem UExpr.subst_eq {s : ULevel.Subst} {a b : UExpr} (h : a ≈ b) : subst s a = subst s b :=
  le_antisymm (subst_mono (UExpr.le_of_equiv h)) (subst_mono (UExpr.le_of_equiv (Setoid.symm h)))

def ULevel.subst (s : ULevel.Subst) (ℓ : ULevel) : ULevel :=
  Quotient.liftOn ℓ (UExpr.subst s) (fun _ _ h => UExpr.subst_eq h)

theorem ULevel.subst_mono {s : ULevel.Subst} {a b : ULevel} (h : a ≤ b) : subst s a ≤ subst s b
  := by induction a, b using Quotient.inductionOn₂; apply UExpr.subst_mono h

@[simp]
theorem ULevel.subst_zero (s : ULevel.Subst) : subst s 0 = 0 := rfl

theorem UExpr.subst_eqv_zero {s : ULevel.Subst} {a : UExpr} (h : a ≈ 0) : subst s a = 0 := by
  rw [<-ULevel.subst_zero]; apply UExpr.subst_eq; exact h

theorem UExpr.subst_imax_eqv_zero {s : ULevel.Subst}
  {a b : UExpr} (h : b ≈ 0) : subst s (a.imax b) = 0 := by
  apply UExpr.subst_eqv_zero; simp [h]

@[simp]
theorem ULevel.subst_uv (s : ULevel.Subst) (u : String) : subst s (ULevel.uv u) = s.get u := rfl

@[simp]
theorem ULevel.subst_succ (s : ULevel.Subst) (ℓ : ULevel) : subst s (ℓ.succ) = (subst s ℓ).succ
  := by induction ℓ using Quotient.inductionOn; rfl

@[simp]
theorem ULevel.subst_sup (s : ULevel.Subst) (a b : ULevel) :
  subst s (a ⊔ b) = (subst s a) ⊔ (subst s b) := by
  induction a, b using Quotient.inductionOn₂; rfl

@[simp]
theorem ULevel.subst_add (s : ULevel.Subst) (ℓ : ULevel) (n : ℕ) :
  subst s (ℓ + n) = (subst s ℓ) + n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [add_succ, subst_succ, ih]; rfl

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
  | imax _ _ Ia Ib =>
    simp at ha
    split at ha
    case isTrue h => rw [UExpr.subst_imax_eqv_zero h, UExpr.subst_imax_eqv_zero h]
    case isFalse h =>
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
