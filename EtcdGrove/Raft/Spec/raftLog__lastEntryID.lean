/-
Port of election_proof/spec_raftLog__lastEntryID.v (feb5c73d4).
-/
import EtcdGrove.Raft.InvRaftPhys
import EtcdGrove.Raft.Plog

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

/-- `l.lastEntryID()`: the id of the last entry, or of the compaction boundary `prev`
when the log after it is empty -- `plogLast` (`Plog.lean`) of the log the protocol sees.

The body (`raftLog.lastEntryID.impl`, `EtcdRaft/Code/go_etcd_io/raft/v3.lean`) is
`lastIndex()` then `term(lastIndex())`, with a `Panicf` on an error from `term`; `term`'s
iff kills it, and its widened postcondition (`plogTermAt … = some t`) pins the term.
Until 2026-10-01 the result was unspecified (only `isUpToDate` read it, and a wrong
answer there could only make the node decline a vote); log replication needs it: the
vote rule now checks the candidate's log is up to date (`plogUpToDate`), and `campaign`
sends it in `MsgVote`. -/
abbrev raftLog.lastEntryID.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"lastEntryID")) (Val #()))
  {{ (e : entryID), RET #e; ownRaftLog l ls ∗
      ⌜e = plogLast ls.prev (ls.sents ++ ls.uents)⌝ }}

end spec

end EtcdGrove
end Perennial
