import Gt3.Syntax.Subst

def Tm.imp {k} (φ ψ : Tm k) : Tm k := .trunc (.arr φ ψ)

def Tm.and {k} (φ ψ : Tm k) : Tm k := .trunc (.prod φ ψ)

def Tm.not {k} (φ : Tm k) : Tm k := .eqn φ .empty

def Tm.or {k} (φ ψ : Tm k) : Tm k := .imp (.not φ) ψ

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
