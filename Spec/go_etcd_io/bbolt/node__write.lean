/-
`n.write(p)` (`node.go`): the node into a page buffer (4d's `WriteInodeToPage`). Users: `node.spill`, `Bucket.write`.
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

/-- (internal) the buffer holds the node's page (4d's `writeNode`), of `nodeSize N` bytes or more. -/
def node.write.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR) (p : Loc) (bs : List w8),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ ∗ bytesPointsto p (DFrac.own 1) bs ∗ ⌜nodeSize N ≤ bs.length⌝ }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"write")) (Val #p))
  {{ RET #(); wtxCore tx γ C ∗ ∃ bs' : List w8, bytesPointsto p (DFrac.own 1) bs' ∗ ⌜bs'.length = bs.length⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
