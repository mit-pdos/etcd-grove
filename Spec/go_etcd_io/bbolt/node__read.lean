/-
`n.read(p)` (`node.go`): the node from a page (4d's `ReadInodeFromPage`). Users: `Bucket.node`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) the node now holds the page's items (leaf or branch as the page says), its page id, its first key. -/
def node.read.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR) (id : w64) (p : Loc) (bs : List w8),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ ∗ txPage tx γ id p bs }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"read")) (Val #p))
  {{ RET #(); ∃ N' : NodeR, wtxCore tx γ { C with nodes := fun x => if x = n then some N' else C.nodes x } ∗ ⌜N'.pgid = id ∧ N'.parent = N.parent⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
