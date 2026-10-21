/-
Port of `election_proof/spec_raftLog__maxAppliableIndex.v` (857d09190).
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `l.maxAppliableIndex(allowUnstable)` (`log.go:265`): `committed`, cut at the last
stable index (`unstable.offset - 1`) unless unstable entries may be applied. The
synchronous `RawNode` passes `true` (`applyUnstableEntries() = !asyncStorageWrites`). -/
abbrev raftLog.maxAppliableIndex.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (au : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"maxAppliableIndex"))
      (Val #au))
  {{ (hi : w64), RET #hi;
      ownRaftLog l ls ∗
      ⌜uint.Z hi = (if au then uint.Z ls.committed
                    else min (uint.Z ls.committed) (logOffset ls - 1))⌝ }}

end spec

end EtcdGrove
end Perennial
