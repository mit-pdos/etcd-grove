/-
Port of `election_proof/spec_raftLog__isUpToDate.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `l.isUpToDate(e)`: whether the candidate's last entry `e` is at least as up to date
as ours, which is the log half of the `MsgVote` check.

The returned boolean is **not** specified, only that the call returns and hands the log
back. That is all the election path needs: answering `false` when it could have
answered `true` makes the node decline to vote, which is always protocol-legal, and
answering `true` is only reachable when the log comparison in `lastEntryID` genuinely
holds. Specifying it would mean relating the entry lists, which the election model does
not mention. -/
abbrev raftLog.isUpToDate.spec : Prop :=
  ∀ (l : Loc) (e : entryID) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"isUpToDate")) (Val #e))
  {{ (b : Bool), RET #b; ownRaftLog l ls }}

end spec

end EtcdGrove
end Perennial
