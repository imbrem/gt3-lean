import Gt3.Syntax.Subst

def Tm.imp {k} (φ ψ : Tm k) : Tm k := .trunc (.arr φ ψ)

def Tm.and {k} (φ ψ : Tm k) : Tm k := .trunc (.prod φ ψ)

def Tm.not {k} (φ : Tm k) : Tm k := .eqn φ .empty

def Tm.or {k} (φ ψ : Tm k) : Tm k := .imp (.not φ) ψ

def Tm.forall {k} (A : Tm k) (φ : Tm (k + 1)) : Tm k := .trunc (.pi A φ)

def Tm.exists {k} (A : Tm k) (φ : Tm (k + 1)) : Tm k := .trunc (.sigma A φ)

@[simp]
theorem Tm.open_imp {k} (φ ψ : Tm (k + 1)) (x : String)
  : (φ.imp ψ).open x = (φ.open x).imp (ψ.open x) := by simp [imp]

@[simp]
theorem Tm.open_and {k} (φ ψ : Tm (k + 1)) (x : String)
  : (φ.and ψ).open x = (φ.open x).and (ψ.open x) := by simp [and]

@[simp]
theorem Tm.open_not {k} (φ : Tm (k + 1)) (x : String)
  : φ.not.open x = (φ.open x).not := by simp [not]

@[simp]
theorem Tm.open_or {k} (φ ψ : Tm (k + 1)) (x : String)
  : (φ.or ψ).open x = (φ.open x).or (ψ.open x) := by simp [or]

@[simp]
theorem Tm.open_forall {k} (A : Tm (k + 1)) (φ : Tm (k + 2)) (x : String)
  : (A.forall φ).open x = (A.open x).forall (φ.open x) := by simp [«forall»]

@[simp]
theorem Tm.open_exists {k} (A : Tm (k + 1)) (φ : Tm (k + 2)) (x : String)
  : (A.exists φ).open x = (A.open x).exists (φ.open x) := by simp [«exists»]

@[simp]
theorem Tm.smul_imp (v : VSubst) {k} (φ ψ : Tm k) : v • (φ.imp ψ) = (v • φ).imp (v • ψ)
  := by simp [imp]

@[simp]
theorem Tm.smul_and (v : VSubst) {k} (φ ψ : Tm k) : v • (φ.and ψ) = (v • φ).and (v • ψ)
  := by simp [and]

@[simp]
theorem Tm.smul_not (v : VSubst) {k} (φ : Tm k) : v • φ.not = (v • φ).not
  := by simp [not]

@[simp]
theorem Tm.smul_or (v : VSubst) {k} (φ ψ : Tm k) : v • (φ.or ψ) = (v • φ).or (v • ψ)
  := by simp [or]

@[simp]
theorem Tm.smul_forall (v : VSubst) {k} (A : Tm k) (φ : Tm (k + 1))
  : v • (A.forall φ) = (v • A).forall (v • φ)
  := by simp [«forall»]

@[simp]
theorem Tm.smul_exists (v : VSubst) {k} (A : Tm k) (φ : Tm (k + 1))
  : v • (A.exists φ) = (v • A).exists (v • φ)
  := by simp [«exists»]
