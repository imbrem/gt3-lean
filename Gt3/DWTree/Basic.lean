import Gt3.Tree.WithLeaf
import Gt3.Utils.Tuple

namespace Gt3

open NumChildren BinderList HasChildren

inductive DWTree (α : Type _) [NumChildren α] : (numLabels : ℕ) → Type _
  | jump
    (tag : α) {numLabels : ℕ}
    (targets : Fin (numChildren tag) → Fin (numLabels))
    : DWTree α numLabels
  | block
    {numLabels numTargets : ℕ}
    (terminator : DWTree α (numLabels + numTargets))
    (subtrees : Fin numTargets → DWTree α (numLabels + numTargets))
    : DWTree α numLabels

end Gt3
