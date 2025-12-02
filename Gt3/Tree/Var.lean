import Gt3.Tree.Node
import Gt3.Tree.Index

namespace Gt3

open NumChildren BinderList HasChildren CastLE

/-- A variable or a value -/
inductive Var (ι : Type _) (α : Type _) : Type _
  | fv (x : ι) : Var ι α
  | val (h : α) : Var ι α

instance Var.instNumChildren {ι α} [NumChildren α] : NumChildren (Var ι α) where
  numChildren
    | .fv _ => 0
    | .val h => numChildren h

instance Var.instBinderList {ι α} [BinderList α] : BinderList (Var ι α) where
  binderList
    | .fv _ => []
    | .val h => binderList h
  getBinder
    | .fv _ => unreachable!
    | .val h => getBinder h
  getBinder_eq h i := by cases h <;> simp only [getBinder_eq] <;> rfl

instance {ι α β} [BinderList α] [HasChildren α β]
  : HasChildren (Var ι α) β where
  getDChild
    | .fv _ => fun i => i.elim0
    | .val h => getDChild h

/-- A de-Bruijn index or a value -/
inductive Ix (α : ℕ → Type _) : ℕ → Type _
  | bv {k} (i : Fin k) : Ix α k
  | val {k} (h : α k) : Ix α k

instance Ix.instNumChildren {α} [∀ k, NumChildren (α k)] {k} : NumChildren (Ix α k) where
  numChildren
    | .bv _ => 0
    | .val h => numChildren h

instance Ix.instBinderList {α} [∀ k, BinderList (α k)] {k} : BinderList (Ix α k) where
  binderList
    | .bv _ => []
    | .val h => binderList h
  getBinder
    | .bv _ => unreachable!
    | .val h => getBinder h
  getBinder_eq h i := by cases h <;> simp only [getBinder_eq] <;> rfl

instance {α} {β : ℕ → ℕ → Type _}
  [∀ k, BinderList (α k)] [∀ k, HasChildren (α k) (β k)] {k} : HasChildren (Ix α k) (β k) where
  getDChild
    | .bv _ => fun i => i.elim0
    | .val h => getDChild h

def Var.map {ι ι' α α'} (f : ι → ι') (g : α → α') : Var ι α → Var ι' α'
  | .fv x => .fv (f x)
  | .val h => .val (g h)

theorem Var.map_id {ι α} (v : Var ι α) : v.map id id = v := by cases v <;> rfl

theorem Var.map_comp {ι ι' ι'' α α' α''}
  (f : ι → ι') (f' : ι' → ι'') (g : α → α') (g' : α' → α'')
  (v : Var ι α) :
  v.map (f' ∘ f) (g' ∘ g) = (v.map f g).map f' g' := by cases v <;> rfl

instance Var.instFunctor {ι} : Functor (Var ι) where
  map := Var.map id

instance Var.instLawfulFunctor {ι} : LawfulFunctor (Var ι) where
  map_const := rfl
  id_map _ := Var.map_id _
  comp_map _ _ _ := Var.map_comp id id _ _ _

instance Var.instMonad {ι} : Monad (Var ι) where
  pure := Var.val
  bind v f := match v with
    | .fv x => .fv x
    | .val h => f h

instance Var.instLawfulMonad {ι} : LawfulMonad (Var ι) where
  seqLeft_eq x y := by cases x <;> rfl
  seqRight_eq x y := by cases x <;> cases y <;> rfl
  pure_seq f x := by cases x <;> rfl
  bind_pure_comp f x := by cases x <;> rfl
  bind_assoc x f g := by cases x <;> rfl
  bind_map x f := by cases x <;> rfl
  pure_bind x f := by rfl

def Ix.map {k k' α α'}
  (f : Fin k → Fin k')
  (g : α k → α' k') : Ix α k → Ix α' k'
  | .bv i => .bv (f i)
  | .val h => .val (g h)

abbrev IxAt (k : ℕ) (α : Type _) := Ix (fun _ => α) k

abbrev IxAt.bv {k : ℕ} {α} (i : Fin k) : IxAt k α := Ix.bv i

abbrev IxAt.val {k : ℕ} {α} (h : α) : IxAt k α := Ix.val h

def IxAt.map {k k' α α'}
  (f : Fin k → Fin k')
  (g : α → α') : IxAt k α → IxAt k' α' :=
  Ix.map f g

instance IxAt.instFunctor {k} : Functor (IxAt k) where
  map := IxAt.map id

instance IxAt.instLawfulFunctor {k} : LawfulFunctor (IxAt k) where
  map_const := rfl
  id_map x := by cases x <;> rfl
  comp_map _ _ x := by cases x <;> rfl

instance IxAt.instMonad {k} : Monad (IxAt k) where
  pure := IxAt.val
  bind v f := match v with
    | .bv i => .bv i
    | .val h => f h

instance IxAt.instLawfulMonad {k} : LawfulMonad (IxAt k) where
  seqLeft_eq x y := by cases x <;> cases y <;> rfl
  seqRight_eq x y := by cases x <;> cases y <;> rfl
  pure_seq f x := by cases x <;> rfl
  bind_pure_comp f x := by cases x <;> rfl
  bind_assoc x f g := by cases x <;> rfl
  bind_map x f := by cases x <;> rfl
  pure_bind x f := by rfl

/-- A locally-nameless term -/
def Ln (ι : Type _) (α : ℕ → Type _) : ℕ → Type _ := Ix (fun n => Var ι (α n))

@[match_pattern]
def Ln.bv {ι α} {k} (i : Fin k) : Ln ι α k := Ix.bv i

@[match_pattern]
def Ln.fv {ι α} {k} (x : ι) : Ln ι α k := Ix.val (Var.fv x)

@[match_pattern]
def Ln.val {ι α} {k} (h : α k) : Ln ι α k := Ix.val (Var.val h)

-- @[eliminator]
-- def Ln.casesOn {ι α k} (t : Ln ι α k)
--   (f_bv : Fin k → Sort _)
--   (f_fv : ι → Sort _)
--   (f_val : α k → Sort _)
--   : Sort _ :=
--   match t with
--   | Ix.bv i => f_bv i
--   | Ix.val (Var.fv x) => f_fv x
--   | Ix.val (Var.val h) => f_val h

def Ln.map {ι ι' α α'} {k k'}
  (f : Fin k → Fin k')
  (g : ι → ι')
  (h : α k → α' k') :
  Ln ι α k → Ln ι' α' k' :=
  Ix.map f (Var.map g h)

abbrev LnAt (k : ℕ) (ι : Type _) (α : Type _) := Ln ι (fun _ => α) k

abbrev LnAt.bv {k : ℕ} {ι α} (i : Fin k) : LnAt k ι α := Ln.bv i

abbrev LnAt.fv {k : ℕ} {ι α} (x : ι) : LnAt k ι α := Ln.fv x

abbrev LnAt.val {k : ℕ} {ι α} (h : α) : LnAt k ι α := Ln.val h

def LnAt.map {k k' ι ι' α α'}
  (f : Fin k → Fin k')
  (g : ι → ι')
  (h : α → α') :
  LnAt k ι α → LnAt k' ι' α' :=
  Ln.map f g h

instance LnAt.instFunctor {k ι} : Functor (LnAt k ι) where
  map := LnAt.map id id

-- instance LnAt.instLawfulFunctor {k ι} : LawfulFunctor (LnAt k ι) where
--   map_const := rfl
--   id_map x := by cases x <;> sorry
--   comp_map _ _ x := by cases x <;> sorry

instance Ln.instNumChildren {ι α} [∀ k, NumChildren (α k)] {k} : NumChildren (Ln ι α k)
  := Ix.instNumChildren

instance Ln.instBinderList {ι α} [∀ k, BinderList (α k)] {k} : BinderList (Ln ι α k)
  := Ix.instBinderList

/-- Extend a binding family with variables -/
inductive VarF (ι : Type _) (α : List ℕ → Type _) : List ℕ → Type _
  | fv (x : ι) : VarF ι α []
  | val {bs} (h : α bs) : VarF ι α bs

/-- Extend a binary family with variables -/
abbrev VarF₂ (ι : Type _) {ν : Type _} (α : List ℕ → ν → Type _) (bs : List ℕ) (k : ν) : Type _
  := VarF ι (fun bs => α bs k) bs

/-- Extend a binary family with de-Bruijn indices -/
inductive IxF₂ (α : List ℕ → ℕ → Type _) : List ℕ → ℕ → Type _
  | bv {k} (i : Fin k) : IxF₂ α [] k
  | val {bs k} (h : α bs k) : IxF₂ α bs k

/-- Extend a family with de-Bruijn indices -/
def IxF (α : List ℕ → Type _) : List ℕ → ℕ → Type _ := IxF₂ (fun bs _ => α bs)

@[match_pattern]
abbrev IxF.bv {α} {k} (i : Fin k) : IxF α [] k := IxF₂.bv i

@[match_pattern]
abbrev IxF.val {α} {bs k} (h : α bs) : IxF α bs k := IxF₂.val h

/-- Extend a binary family with variables and de-Bruijn indices -/
def LnF₂ (ι : Type _) (α : List ℕ → ℕ → Type _) : List ℕ → ℕ → Type _ := IxF₂ (VarF₂ ι α)

abbrev LnF₂.bv {ι α} {k} (i : Fin k) : LnF₂ ι α [] k := IxF₂.bv i

abbrev LnF₂.fv {ι α} {k} (x : ι) : LnF₂ ι α [] k := IxF₂.val (VarF.fv x)

abbrev LnF₂.val {ι α} {k bs} (h : α k bs) : LnF₂ ι α k bs := IxF₂.val (VarF.val h)

/-- Extend a binding family with variables and de-Bruijn indices -/
abbrev LnF (ι : Type) (α : List ℕ → Type _) : List ℕ → ℕ → Type _ := IxF (VarF ι α)

abbrev LnF.bv {ι α} {k} (i : Fin k) : LnF ι α [] k := LnF₂.bv i

abbrev LnF.fv {ι α} {k} (x : ι) : LnF ι α [] k := LnF₂.fv x

abbrev LnF.val {ι α} {k bs} (h : α bs) : LnF ι α bs k := LnF₂.val h

instance IxF₂.instCastLE {α} [ha : ∀ {bs}, CastLE (α bs)] {bs} : CastLE (IxF₂ α bs) where
  castLE h
  | .bv i => .bv (i.castLE h)
  | .val v => .val (castLE h v)
  castLE_refl x := by cases x <;> simp
  castLE_castLE _ _ x := by cases x <;> simp

@[simp]
theorem IxF₂.castLE_bv {α} [ha : ∀ {bs}, CastLE (α bs)] {lo hi} (h : lo ≤ hi) (i : Fin lo)
  : castLE h (IxF₂.bv (α := α) i) = IxF₂.bv (i.castLE h)
  := rfl

@[simp]
theorem IxF₂.castLE_val {α} [ha : ∀ {bs}, CastLE (α bs)] {lo hi} (h : lo ≤ hi) {bs} (v : α bs lo)
  : castLE h (IxF₂.val (α := α) v) = IxF₂.val (castLE h v)
  := rfl

instance IxF₂.instNumChildren {α} [∀ {bs k}, NumChildren (α bs k)] {bs k}
  : NumChildren (IxF₂ α bs k) where
  numChildren
    | .bv _ => 0
    | .val h => numChildren h

@[simp]
theorem IxF₂.numChildren_bv {α} [∀ {bs k}, NumChildren (α bs k)] {k} (i : Fin k)
  : numChildren (IxF₂.bv (α := α) i) = 0
  := rfl

@[simp]
theorem IxF₂.numChildren_val {α} [∀ {bs k}, NumChildren (α bs k)] {bs k} (v : α bs k)
  : numChildren (IxF₂.val (α := α) v) = numChildren v
  := rfl

instance IxF₂.instBinderList {α} [∀ {bs k}, BinderList (α bs k)] {bs k}
  : BinderList (IxF₂ α bs k) where
  binderList
    | .bv _ => []
    | .val h => binderList h
  getBinder
    | .bv _ => unreachable!
    | .val h => getBinder h
  getBinder_eq h i := by cases h <;> simp only [getBinder_eq] <;> rfl

@[simp]
theorem IxF₂.binderList_bv {α} [∀ {bs k}, BinderList (α bs k)] {k} (i : Fin k)
  : binderList (IxF₂.bv (α := α) i) = []
  := rfl

@[simp]
theorem IxF₂.binderList_val {α} [∀ {bs k}, BinderList (α bs k)] {bs k} (v : α bs k)
  : binderList (IxF₂.val (α := α) v) = binderList v
  := rfl

@[simp]
theorem IxF₂.getBinder_val {α} [∀ {bs k}, BinderList (α bs k)] {bs k} (v : α bs k)
  : getBinder (IxF₂.val (α := α) v) = getBinder v
  := rfl

instance IxF₂.instBindCastLE
  {α} [∀ {bs k}, BinderList (α bs k)] [ha : ∀ {bs}, BindCastLE (α bs)] {bs}
  : BindCastLE (IxF₂ α bs) where
  castLE_binderHom _ := BinderListHom.mk' (fun x => by cases x <;> simp)

instance IxF.instCastLE {α bs} : CastLE (IxF α bs) := IxF₂.instCastLE

@[simp]
theorem IxF.castLE_bv {α} {lo hi} (h : lo ≤ hi) (i : Fin lo)
  : castLE h (IxF.bv (α := α) i) = IxF.bv (i.castLE h)
  := rfl

@[simp]
theorem IxF.castLE_val {α} {lo hi} (h : lo ≤ hi) {bs} (v : α bs)
  : castLE h (IxF.val (α := α) v) = IxF.val v
  := rfl

instance IxF.instNumChildren {α bs k} [∀ {bs}, NumChildren (α bs)] : NumChildren (IxF α bs k)
  := IxF₂.instNumChildren

@[simp]
theorem IxF.numChildren_bv {α} [∀ {bs}, NumChildren (α bs)] {k} (i : Fin k)
  : numChildren (IxF.bv (α := α) i) = 0
  := rfl

@[simp]
theorem IxF.numChildren_val {α} [∀ {bs}, NumChildren (α bs)] {bs k} (v : α bs)
  : numChildren (IxF.val (α := α) (k := k) v) = numChildren v
  := rfl

instance IxF.instBinderList {α bs k} [∀ {bs}, BinderList (α bs)] : BinderList (IxF α bs k)
  := IxF₂.instBinderList

@[simp]
theorem IxF.binderList_bv {α} [∀ {bs}, BinderList (α bs)] {k} (i : Fin k)
  : binderList (IxF.bv (α := α) i) = []
  := rfl

@[simp]
theorem IxF.binderList_val {α} [∀ {bs}, BinderList (α bs)] {bs k} (v : α bs)
  : binderList (IxF.val (α := α) (k := k) v) = binderList v
  := rfl

instance IxF.instBindCastLE {α bs} [∀ {bs}, BinderList (α bs)] : BindCastLE (IxF α bs)
  := IxF₂.instBindCastLE

instance LnF.instCastLE {ι α bs} : CastLE (LnF ι α bs)
  := IxF.instCastLE

def IxF.lastCases {α bs k} {motive : ∀ {bs}, IxF α bs (k + 1) → Type _}
  (last : motive (.bv (Fin.last k)))
  (bv : ∀ i : Fin k, motive (.bv i.castSucc))
  (val : ∀ h : α bs, motive (.val h))
  : (h : IxF α bs (k + 1)) → motive h
  | .bv i => i.lastCases last bv
  | .val h => val h

def IxF.lastCases' {α bs k} {motive : ∀ (bs), IxF α bs (k + 1) → Type _}
  (last : motive [] (.bv (Fin.last k)))
  (rest : ∀ h : IxF α bs k, motive bs (castSucc h))
  : (h : IxF α bs (k + 1)) → motive bs h
  | .bv i => i.lastCases last (fun i => rest (.bv i))
  | .val h => rest (.val h)

def LnF.lastCases' {ι α bs k} {motive : ∀ (bs), LnF ι α bs (k + 1) → Type _}
  (last : motive [] (.bv (Fin.last k)))
  (rest : ∀ h : LnF ι α bs k, motive bs (castSucc h))
  : (h : LnF ι α bs (k + 1)) → motive bs h
  := IxF.lastCases' last rest

def LnF.open {ι α k bs} (x : ι) : LnF ι α bs (k + 1) → LnF ι α bs k
  := LnF.lastCases' (motive := fun bs _ => LnF ι α bs k) (LnF.fv x) id

end Gt3
