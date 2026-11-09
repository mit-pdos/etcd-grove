/-
`n.splitTwo(pageSize)` (`node.go`): small nodes stay; else the inodes split at `splitIndex(splitThreshold(...))` into `n` and a new sibling (a new parent if none).
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

/-- (internal) either `n` alone, or `n` and a sibling holding the inodes after the split point. -/
def node.splitTwo.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR) (ps : w64),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"splitTwo")) (Val #ps))
  {{ (a b : Loc), RET (PairV #a #b); ∃ C' : TxCore, wtxCore tx γ C' ∗ ⌜a = n ∧ (b = Loc.null ∨ ∃ A B, C'.nodes n = some A ∧ C'.nodes b = some B ∧ A.inodes ++ B.inodes = N.inodes ∧ 2 ≤ A.inodes.length ∧ 2 ≤ B.inodes.length ∧ B.isLeaf = N.isLeaf)⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
