/-
`n.childIndex(child)` (`node.go`): `sort.Search` on the child's key.
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

/-- (internal) the first inode not below the child's key. -/
def node.childIndex.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR) (ch : Loc) (CH : NodeR),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ ∗ ⌜C.nodes ch = some CH⌝ }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"childIndex")) (Val #ch))
  {{ (z : w64), RET #z; wtxCore tx γ C ∗ ⌜uint.nat z = nodeInsIdx N CH.key⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
