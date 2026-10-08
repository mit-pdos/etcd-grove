/-
Port of election_proof/spec_raftLog__hasNextOrInProgressSnapshot.v (feb5c73d4).
-/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `l.hasNextOrInProgressSnapshot()` is `l.unstable.snapshot != nil`: whether a
snapshot is pending (`LogState.snap`). `promotable` calls it -- a node with a pending
snapshot does not campaign. (Added back 2026-09-16, when `promotable` stopped being an
axiom; until 2026-10-02 it returned `false` outright, no snapshot being in scope.) -/
abbrev raftLog.hasNextOrInProgressSnapshot.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"hasNextOrInProgressSnapshot"))
      (Val #()))
  {{ (b : Bool), RET #b; ownRaftLog l ls ∗ ⌜b = decide (ls.snap ≠ none)⌝ }}

end spec

end EtcdGrove
end Perennial
