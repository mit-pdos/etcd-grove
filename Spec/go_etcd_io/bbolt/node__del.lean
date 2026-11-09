/-
`n.del(key)` (`node.go`). Users: `Bucket.Delete`, `DeleteBucket`, `Cursor.Delete`, `node.rebalance`.
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

/-- (internal) the inode at `key` removed, if any (`NodeR.del`). -/
def node.del.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ ∗ key ↦*{dk} kb }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"del")) (Val #key))
  {{ RET #(); key ↦*{dk} kb ∗ wtxCore tx γ { C with nodes := fun x => if x = n then some (N.del kb) else C.nodes x } }}

end spec

end Bbolt
end EtcdGrove
end Perennial
