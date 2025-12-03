import Gt3.Tree.Basic

namespace Gt3

open NumChildren BinderList HasChildren

def WithNull (α : Type _) : Type _ := Option α

@[match_pattern]
def WithNull.tag {α} (a : α) : WithNull α := some a

@[match_pattern]
def WithNull.null {α} : WithNull α := none

@[cases_eliminator, induction_eliminator]
def WithNull.casesOn {α} {motive : WithNull α → Sort _}
  (h_tag : ∀ a : α, motive (.tag a))
  (h_null : motive .null)
  : (t : WithNull α) → motive t
  | .tag a => h_tag a
  | .null   => h_null

instance WithNull.instEmptyCollection {α} : EmptyCollection (WithNull α) where
  emptyCollection := WithNull.null

instance WithNull.instNumChildren {α} [NumChildren α] : NumChildren (WithNull α) where
  numChildren
    | .tag h => numChildren h
    | .null     => 0

instance WithNull.instBinderList {α} [BinderList α] : BinderList (WithNull α) where
  binderList
    | .tag h => binderList h
    | .null     => []
  getBinder
    | .tag h => getBinder h
    | .null  => unreachable!
  getBinder_eq h := by intro i; cases h <;> simp only [getBinder_eq] <;> rfl

instance WithNull.instHasChildren
  {α β} [BinderList α] [HasChildren α β] : HasChildren (WithNull α) β where
  getDChild
    | .tag h => getDChild h
    | .null => fun i => i.elim0

instance WithNull.instMonad : Monad WithNull where
  pure := WithNull.tag
  bind t f :=
    match t with
    | .tag a => f a
    | .null  => .null

instance WithNull.instLawfulMonad : LawfulMonad WithNull := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun x f => by simp [bind])
  (bind_assoc := fun x f g => by cases x <;> rfl)

@[simp]
theorem WithNull.null_bind {α β} (f : α → WithNull β) :
  (WithNull.null : WithNull α) >>= f = WithNull.null := rfl

@[simp]
theorem WithNull.tag_bind {α β} (a : α) (f : α → WithNull β) :
  (WithNull.tag a) >>= f = f a := rfl

inductive WithNull.liftRel {α β} (rel : α → β → Prop) : WithNull α → WithNull β → Prop
  | tag {a b} (h : rel a b) : liftRel rel (.tag a) (.tag b)
  | null : liftRel rel .null .null

instance WithNull.liftRel.instIsRefl {α} (rel : α → α → Prop)
  [hrel : IsRefl α rel] : IsRefl (WithNull α) (liftRel rel) where
  refl a := by cases a <;> constructor; apply IsRefl.refl

instance WithNull.liftRel.instIsSymm {α} (rel : α → α → Prop)
  [hrel : IsSymm α rel] : IsSymm (WithNull α) (liftRel rel) where
  symm _ _ h := by cases h <;> constructor; apply IsSymm.symm; assumption

instance WithNull.liftRel.instIsTrans {α} (rel : α → α → Prop)
  [hrel : IsTrans α rel] : IsTrans (WithNull α) (liftRel rel) where
  trans _ _ _ h1 h2 := by cases h1 <;> cases h2 <;> constructor; apply IsTrans.trans <;> assumption

instance WithNull.setoid {α} [Setoid α] : Setoid (WithNull α) where
  r := WithNull.liftRel Setoid.r
  iseqv := ⟨
    fun x => (liftRel.instIsRefl (hrel := ⟨fun x => Setoid.iseqv.refl x⟩)).refl x,
    fun h => (liftRel.instIsSymm (hrel := ⟨fun _ _ h => Setoid.iseqv.symm h⟩)).symm _ _ h,
    fun h1 h2 =>
    (liftRel.instIsTrans (rel := Setoid.r)
      (hrel := ⟨fun _ _ _ h1 h2 => Setoid.iseqv.trans h1 h2⟩)).trans _ _ _ h1 h2
  ⟩

end Gt3
