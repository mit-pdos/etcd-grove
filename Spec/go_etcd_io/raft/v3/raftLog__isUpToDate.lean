/-
Port of election_proof/spec_raftLog__isUpToDate.v (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.Plog

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

/-- `l.isUpToDate(e)`: whether the candidate's last entry `e` is at least as up to date
as ours, which is the log half of the `MsgVote` check: `plogUpToDate` (`Plog.lean`) of
the log the protocol sees.

Pinned since 2026-10-01 (before, only "returns and hands the log back"): with a log in
the protocol model, granting a vote records that this check passed (`Step.grantVote`'s
premise), which leader completeness depends on. The body (`raftLog.isUpToDate.impl`,
`Code/go_etcd_io/raft/v3.lean`) is `lastEntryID()` and a short-circuit
comparison, so this is `lastEntryID`'s widened spec plus the two `Bool` connectives. -/
abbrev raftLog.isUpToDate.spec : Prop :=
  ∀ (l : Loc) (e : entryID) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"isUpToDate")) (Val #e))
  {{ (b : Bool), RET #b; ownRaftLog l ls ∗
      ⌜b = plogUpToDate ls.prev (ls.sents ++ ls.uents) e⌝ }}

end spec

end EtcdGrove
end Perennial
