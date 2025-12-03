import Mathlib.Data.Fin.Tuple.Basic

def mapFinAdd {n m n' m' : ℕ}
  (f : Fin n → Fin n') (g : Fin m → Fin m')
  : Fin (n + m) → Fin (n' + m') :=
  Fin.append (Fin.castAdd m' ∘ f) (Fin.natAdd n' ∘ g)

@[simp]
theorem mapFinAdd_id_id {n m : ℕ}
  : mapFinAdd (n := n) (m := m) id id = id := by ext i; simp [mapFinAdd, Fin.append, Fin.addCases]

theorem append_mapFinAdd {n m n' m' : ℕ} {α}
  (f : Fin n → Fin n') (g : Fin m → Fin m')
  (left : Fin n' → α) (right : Fin m' → α) (i)
  : Fin.append left right (mapFinAdd f g i) = Fin.append (left ∘ f) (right ∘ g) i
  := by
    simp only [Fin.append, Fin.addCases, mapFinAdd, Function.comp_apply, eq_rec_constant,
      Fin.castAdd_castLT]
    split <;> simp [*]

theorem append_comp_mapFinAdd {n m n' m' : ℕ} {α}
  (f : Fin n → Fin n') (g : Fin m → Fin m')
  (left : Fin n' → α) (right : Fin m' → α)
  : Fin.append left right ∘ mapFinAdd f g = Fin.append (left ∘ f) (right ∘ g)
  := funext fun i => append_mapFinAdd f g left right i

theorem mapFinAdd_comp_mapFinAdd {n₁ m₁ n₂ m₂ n₃ m₃ : ℕ}
  (f₁ : Fin n₁ → Fin n₂) (g₁ : Fin m₁ → Fin m₂)
  (f₂ : Fin n₂ → Fin n₃) (g₂ : Fin m₂ → Fin m₃)
  : mapFinAdd f₂ g₂ ∘ mapFinAdd f₁ g₁ = mapFinAdd (f₂ ∘ f₁) (g₂ ∘ g₁)
  := by rw [mapFinAdd, append_comp_mapFinAdd]; rfl

theorem mapFinAdd_mapFinAdd {n₁ m₁ n₂ m₂ n₃ m₃ : ℕ}
  (f₁ : Fin n₁ → Fin n₂) (g₁ : Fin m₁ → Fin m₂)
  (f₂ : Fin n₂ → Fin n₃) (g₂ : Fin m₂ → Fin m₃) (i)
  : (mapFinAdd f₂ g₂ (mapFinAdd f₁ g₁ i)) = mapFinAdd (f₂ ∘ f₁) (g₂ ∘ g₁) i
  := congrFun (mapFinAdd_comp_mapFinAdd f₁ g₁ f₂ g₂) i

theorem mapFinAdd_zero' {n m : ℕ}
  (f : Fin n → Fin m) (g : Fin 0 → Fin 0)
  : mapFinAdd f g = f := by ext i; simp [mapFinAdd, Fin.append, Fin.addCases]; rfl

theorem fin_src_eq_zero {n} (f : Fin n → Fin 0) : n = 0
  := match n with | 0 => rfl | _ + 1 => (f 0).elim0

theorem mapFinAdd_zero {n n' m : ℕ}
  (f : Fin n → Fin n') (g : Fin m → Fin 0)
  : mapFinAdd f g = f ∘ Fin.cast (by simp [fin_src_eq_zero g])
  := by cases fin_src_eq_zero g; simp [mapFinAdd_zero']

theorem zero_mapFinAdd {n m m' : ℕ}
  (f : Fin n → Fin 0) (g : Fin m → Fin m')
  : mapFinAdd f g = Fin.cast (by simp) ∘ g ∘ Fin.cast (by simp [fin_src_eq_zero f])
  := by
  cases fin_src_eq_zero f
  ext i
  simp [mapFinAdd, Fin.append, Fin.addCases]
