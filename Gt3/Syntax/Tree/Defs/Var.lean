import Gt3.Syntax.Tree.Children

namespace Gt3

open NumChildren BinderList HasChildren

/-- A variable or a value -/
inductive Var (ι : Type _) (α : Type _) : Type _
  | fv (x : ι) : Var ι α
  | val (h : α) : Var ι α

instance {ι α} [NumChildren α] : NumChildren (Var ι α) where
  numChildren
    | .fv _ => 0
    | .val h => numChildren h

instance {ι α} [BinderList α] : BinderList (Var ι α) where
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

instance {α} [∀ k, NumChildren (α k)] {k} : NumChildren (Ix α k) where
  numChildren
    | .bv _ => 0
    | .val h => numChildren h

instance {α} [∀ k, BinderList (α k)] {k} : BinderList (Ix α k) where
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

end Gt3
