/-
Port of election_proof/spec_raftLog__findConflict.v (feb5c73d4).

Lean notes:
* The reference `raftLog__findConflictⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:634` is to
  the Lean generated code `raftLog.findConflict.impl`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog
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

/-- `l.findConflict(s)` (etcd-io/raft#155, `notes/pr-verify/raft-155.md`): whether the log has
`s.prev`, and if it does the id of the last entry of `s` the log has before the first one it
does not -- `s.prev` if the first entry already mismatches -- which is `plogFindMatch`
(`Plog.lean`).

The body (`raftLog.findConflict.impl`, `Code/go_etcd_io/raft/v3.lean`):

    if !l.matchTerm(s.prev) { return entryID{}, false }
    match := s.prev
    for i := range s.entries {
        id := pbEntryID(&s.entries[i])
        if l.matchTerm(id) { match = id; continue }
        if id.index <= l.lastIndex() {
            l.logger.Infof("found conflict ...", id.index,
                l.zeroTermOnOutOfBounds(l.term(id.index)), id.term)
        }
        return match, true
    }
    return match, true

Postcondition: `ok` is whether `s.prev` matches; when it does, the id is `plogFindMatch`,
otherwise `entryID{}` (which the one caller, `maybeAppend`, does not read). What the doc comment promises
of the id (it is in `[s.prev.index, s.lastIndex()]`, every entry up to it is in the log, the
next is not) is `plogFindMatch_drop` (`Plog.lean`), for a well-formed slice.

**Premise**: `s` is a well-formed log slice (`PlogWf s.prev ents`: contiguous indices after
`s.prev`, what `logSlice.valid` would check and the doc comment's range claim needs). Nothing
checks it on the `MsgApp` path (`logSliceFromMsgApp` does not call `valid`): it is the
caller's premise, ultimately an assumption that the leader sends well-formed appends
(`raft__handleAppendEntries.lean`). Without it the PR's fast-forward misbehaves where the old
code did not (`notes/pr-verify/raft-155.md`, "Findings"). It also
places every entry above `s.prev`, so above the compaction boundary once `s.prev` has
matched: at a conflicting entry with `id.index <= lastIndex()` `term` returns a `nil` error,
what `zeroTermOnOutOfBounds`'s spec takes (the role of the old spec's premise). Before
etcd-io/raft#155 the function took `[]*Entry` and returned the first conflict's index
(`plogFindConflict`); `maybeAppend` did the `prev` check itself.

The batch is lent at any fraction and comes back; the log is unchanged. -/
abbrev raftLog.findConflict.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (s : logSlice) (dq : DFrac) (ents : List EntryM),
  PlogWf s.prev' ents →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls ∗
      "Hes" ∷ entsPts s.entries' dq ents }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"findConflict")) (Val #s))
  {{ (m : entryID) (ok : Bool), RET (PairV #m #ok);
      ownRaftLog l ls ∗ entsPts s.entries' dq ents ∗
      ⌜ok = decide (PlogMatches ls.prev (ls.sents ++ ls.uents) s.prev') ∧
        (ok = true → m = plogFindMatch ls.prev (ls.sents ++ ls.uents) s.prev' ents) ∧
        (ok = false → m = zero_val entryID)⌝ }}

end spec

end EtcdGrove
end Perennial
