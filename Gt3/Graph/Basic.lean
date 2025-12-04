import Gt3.Tree.Node
import Gt3.Cotree.SimIx

namespace Gt3

open NumChildren BinderList HasChildren FlatChildren

structure Graph (ι : Type _) (α : Type _) [NumChildren α] where
  nodes : ι → Node α ι

end Gt3
