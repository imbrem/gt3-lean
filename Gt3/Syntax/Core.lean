import Gt3.Tree.Var
import Gt3.Syntax.Tag

namespace Gt3

open NumChildren BinderList CastLE

/-- A core-shaped de-Bruijn tree -/
inductive DCoreTree (α : List ℕ → ℕ → Type _) : ℕ → Type _ where
  | constant {k} (h : α [] k) : DCoreTree α k
  | unary {k} (h : α [0] k) (arg : DCoreTree α k) : DCoreTree α k
  | binary {k} (h : α [0, 0] k) (left right : DCoreTree α k) : DCoreTree α k
  | binder {k} (h : α [0, 1] k)
      (bound : DCoreTree α k)
      (body : DCoreTree α (k + 1))
      : DCoreTree α k
  | ite {k} (h : α [0, 1, 1] k)
      (cond : DCoreTree α k)
      (thenBr : DCoreTree α (k + 1))
      (elseBr : DCoreTree α (k + 1))
      : DCoreTree α k
  | natrec {k} (h : α [1, 1, 0, 0] k)
      (mot : DCoreTree α (k + 1))
      (succCase : DCoreTree α (k + 1))
      (zeroCase : DCoreTree α k)
      (scrut : DCoreTree α k)
      : DCoreTree α k

def DCoreTree.castLE' {α : List ℕ → Type _}
  {lo hi : ℕ} (hk : lo ≤ hi)
  : DCoreTree (IxF α) lo → DCoreTree (IxF α) hi
  | .constant h => .constant (castLE hk h)
  | .unary (.val h) arg => .unary (.val h) (arg.castLE' hk)
  | .binary (.val h) left right => .binary (.val h) (left.castLE' hk) (right.castLE' hk)
  | .binder (.val h) bound body
    => .binder (.val h) (bound.castLE' hk) (body.castLE' (by omega))
  | .ite (.val h) cond thenBr elseBr
    => .ite (.val h) (cond.castLE' hk) (thenBr.castLE' (by omega)) (elseBr.castLE' (by omega))
  | .natrec (.val h) mot succCase zeroCase scrut
    => .natrec (.val h) (mot.castLE' (by omega)) (succCase.castLE' (by omega))
                     (zeroCase.castLE' hk) (scrut.castLE' hk)

def DCoreTree.replaceConst {ι} {α : List ℕ → Type _}
  (σ : ∀ {k}, LnF ι α [] (k + 1) → DCoreTree (LnF ι α) k) {k}
  :  DCoreTree (LnF ι α) (k + 1) → DCoreTree (LnF ι α) k
  | .constant h => σ h
  | .unary (.val h) arg => .unary (.val h) (arg.replaceConst σ)
  | .binary (.val h) left right => .binary (.val h) (left.replaceConst σ) (right.replaceConst σ)
  | .binder (.val h) bound body => .binder (.val h) (bound.replaceConst σ) (body.replaceConst σ)
  | .ite (.val h) cond thenBr elseBr
    => .ite (.val h) (cond.replaceConst σ) (thenBr.replaceConst σ) (elseBr.replaceConst σ)
  | .natrec (.val h) mot succCase zeroCase scrut =>
      .natrec (.val h) (mot.replaceConst σ) (succCase.replaceConst σ)
                       (zeroCase.replaceConst σ) (scrut.replaceConst σ)

def DCoreTree.openConst {ι} {α : List ℕ → Type _} {k}
  (x : ι) (h : LnF ι α [] (k + 1)) : DCoreTree (LnF ι α) k
  := .constant (h.open x)

def DCoreTree.open {ι} {α : List ℕ → Type _} {k}
  (x : ι) (t : DCoreTree (LnF ι α) (k + 1)) : DCoreTree (LnF ι α) k
  := t.replaceConst (openConst x)

def DCoreTree.lsIx {α : List ℕ → Type _} {k}
  (a : DCoreTree (IxF α) 0) (h : IxF α [] (k + 1)) : DCoreTree (IxF α) k
  := h.lastCases'
    (motive := fun _ _ => DCoreTree (IxF α) k) (a.castLE' (by omega)) DCoreTree.constant

def DCoreTree.ls {ι} {α : List ℕ → Type _} {k}
  (a : DCoreTree (LnF ι α) 0) (t : DCoreTree (LnF ι α) (k + 1)) : DCoreTree (LnF ι α) k
  := t.replaceConst a.lsIx

/-- A core-shaped tree -/
inductive CoreTree (α : List ℕ → Type _) : Type _ where
  | constant (h : α []) : CoreTree α
  | unary (h : α [0]) (arg : CoreTree α) : CoreTree α
  | binary (h : α [0, 0]) (left right : CoreTree α) : CoreTree α
  | binder (h : α [0, 1]) (body : CoreTree α) (ty : CoreTree α) : CoreTree α
  | ite (h : α [0, 1, 1]) (cond thenBr elseBr : CoreTree α) : CoreTree α
  | natrec (h : α [1, 1, 0, 0])
      (mot : CoreTree α)
      (succCase : CoreTree α)
      (zeroCase : CoreTree α)
      (scrut : CoreTree α)
      : CoreTree α

/-- A forded core-shaped tree -/
inductive FCoreTree (α : Type _) [BinderList α] : Type _ where
  | constant (h : α) (hh : binderList h = []) : FCoreTree α
  | unary (h : α) (hh : binderList h = [0]) (arg : FCoreTree α) : FCoreTree α
  | binary (h : α) (hh : binderList h = [0, 0]) (left right : FCoreTree α) : FCoreTree α
  | binder (h : α) (hh : binderList h = [0, 1])
      (body : FCoreTree α)
      (ty : FCoreTree α)
      : FCoreTree α
  | ite (h : α) (hh : binderList h = [0, 1, 1])
      (cond : FCoreTree α)
      (thenBr : FCoreTree α)
      (elseBr : FCoreTree α)
      : FCoreTree α
  | natrec (h : α) (hh : binderList h = [1, 1, 0, 0])
      (mot : FCoreTree α)
      (succCase : FCoreTree α)
      (zeroCase : FCoreTree α)
      (scrut : FCoreTree α)
      : FCoreTree α

/-- A fordered core-shaped de-Bruijn tree -/
inductive FDCoreTree (α : Type _) [BinderList α] : ℕ → Type _ where
  | constant {k} (h : α) (hh : binderList h = []) : FDCoreTree α k
  | unary {k} (h : α) (hh : binderList h = [0]) (arg : FDCoreTree α k) : FDCoreTree α k
  | binary {k} (h : α) (hh : binderList h = [0, 0]) (left right : FDCoreTree α k) : FDCoreTree α k
  | binder {k} (h : α) (hh : binderList h = [0, 1])
      (body : FDCoreTree α (k + 1))
      (ty : FDCoreTree α k)
      : FDCoreTree α k
  | ite {k} (h : α) (hh : binderList h = [0, 1, 1])
      (cond : FDCoreTree α k)
      (thenBr : FDCoreTree α (k + 1))
      (elseBr : FDCoreTree α (k + 1))
      : FDCoreTree α k
  | natrec {k} (h : α) (hh : binderList h = [1, 1, 0, 0])
      (mot : FDCoreTree α (k + 1))
      (succCase : FDCoreTree α (k + 1))
      (zeroCase : FDCoreTree α k)
      (scrut : FDCoreTree α k)
      : FDCoreTree α k

end Gt3
