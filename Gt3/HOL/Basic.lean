import Gt3.JEq.Basic
import Gt3.Syntax.Erase

namespace Gt3

inductive FCtx : ℕ → Type
| nil {k} : FCtx k
| cons {k} (Γ : FCtx k) (x : String) (A : Tm k) : FCtx k

inductive TmCat : Type
| open
| closed

inductive StmtCat : Type
| formula
| fact

inductive SynCat : Type
| sym
| msubst : SynCat
| tm : TmCat → SynCat
| stmt : StmtCat → SynCat
| func : SynCat → SynCat

abbrev SynCat.otm : SynCat := .tm .open

abbrev SynCat.ltm : SynCat := .tm .closed

abbrev SynCat.formula : SynCat := .stmt .formula

abbrev SynCat.fact : SynCat := .stmt .fact

inductive HOL : SynCat → ℕ → Type
| fv {c k} : String → HOL c k
| bv {c k} : Fin k → HOL c k
| syn_eq {c k} : HOL c k → HOL c k → HOL c k
| tm {c k} : Tm k → HOL (.tm c) k
| otm {k} : OTm → HOL .otm k
| tt {c k} : HOL (.stmt c) k
| ff {c k} : HOL (.stmt c) k
| and {c k} : HOL (.stmt c) k → HOL (.stmt c) k → HOL (.stmt c) k
| or {c k} : HOL (.stmt c) k → HOL (.stmt c) k → HOL (.stmt c) k
| imp {c k} : HOL (.stmt c) k → HOL (.stmt c) k → HOL (.stmt c) k
| forall_ {c k} : SynCat → HOL (.stmt c) (k + 1) → HOL (.stmt c) k
| exists_ {c k} : SynCat → HOL (.stmt c) (k + 1) → HOL (.stmt c) k
| seq {k} : FCtx k → HOL .formula k → HOL .fact k

end Gt3
