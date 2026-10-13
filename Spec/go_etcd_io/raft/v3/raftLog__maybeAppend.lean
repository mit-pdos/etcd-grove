/-
Port of election_proof/spec_raftLog__maybeAppend.v (feb5c73d4).

Lean notes:
* `plog_wf`, `plog_matches`, `plog_find_conflict`, `plog_maybe_append`,
  `plog_commit_to` are `PlogWf`, `PlogMatches`, `plogFindConflict`, `plogMaybeAppend`,
  `plogCommitTo` (`Plog.lean`). `Forall (λ e, …) ents` is `∀ e ∈ ents, …`;
  `own_slice_cap raftpb.Entry.t s (DfracOwn 1)` is `ownSliceCap raftpb.Entry s
  (DFrac.own 1)`; `(#lastnewi, #ok)` is `PairV #lastnewi #ok`;
  `if decide (…) then committed else lni` is kept as `if … then … else …`.
* The reference `raftLog__maybeAppendⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:546` is to
  the Lean generated code `raftLog.maybeAppend.impl`.
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

/-- `l.maybeAppend(a, committed)`: a follower's handling of a `MsgApp`'s entries --
`plogMaybeAppend` (`Plog.lean`) plus the commit.

The body (`raftLog.maybeAppend.impl`, `Code/go_etcd_io/raft/v3.lean`):

    if !l.matchTerm(a.prev) { return 0, false }
    lastnewi = a.prev.index + uint64(len(a.entries))
    ci := l.findConflict(a.entries)
    switch {
    case ci == 0:
    case ci <= l.committed: l.logger.Panicf(...)
    default:
        offset := a.prev.index + 1
        if ci-offset > uint64(len(a.entries)) { l.logger.Panicf(...) }
        l.append(a.entries[ci-offset:]...)
    }
    l.commitTo(min(committed, lastnewi))
    return lastnewi, true

Postcondition: when `a.prev` does not match, `(0, false)` and the log unchanged;
otherwise `(lastnewi, true)`, the entries are `plogMaybeAppend`'s, and `committed` is
raised to `min(committed, lastnewi)` (`plogCommitTo`), and `applying`, the pending
snapshot and `unpersisted` are kept (2026-10-09; `inprogress` is not: a truncation
moves it back).

Premises, one per way the body could go wrong:
- the batch is a well-formed log slice after `a.prev` (`PlogWf a.prev ents`) and
  `a.prev.index + |ents| + 1 < 2^64`: what `findConflict`, `append` and the no-wrap of
  the new log need; it also makes the second `Panicf` (`ci - offset > len`) dead -- the
  design's "arithmetic" fact;
- **the conflict fact** (`raft-replication-model.md`, "Protocol facts the code needs",
  `app_no_conflict_below_commit`): if `a.prev` matches, the conflict index is `0` or
  above `committed`. It kills the first `Panicf` and is `append`'s
  `committed < ents[0].Index`. (Until 2026-10-13 also: no configuration change in the
  batch, `append`'s scope premise.)
`commitTo`'s premise is *not* a premise here: after the append the log reaches
`lastnewi`, so `min(committed, lastnewi)` is inside it.

**The batch's slice** is taken read-only with its capacity, and the capacity is not
returned: `append` may adopt `a.entries[ci-offset:]` as `u.entries`
(`Spec/raftLog__append.lean`), after which raft's own later `append`s write into its
slack. So the caller must own that slack (for a `MsgApp` handed to `Step`, the
message's `Entries` buffer). -/
abbrev raftLog.maybeAppend.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (a : logSlice) (ents : List raftpb.Entry) (committed : w64),
  PlogWf a.prev' ents →
  uint.Z a.prev'.index' + (ents.length : Int) + 1 < 2 ^ 64 →
  (PlogMatches ls.prev (ls.sents ++ ls.uents) a.prev' →
   plogFindConflict ls.prev (ls.sents ++ ls.uents) ents = W64 0 ∨
   uint.Z ls.committed < uint.Z (plogFindConflict ls.prev (ls.sents ++ ls.uents) ents)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls ∗
      "#Hents" ∷ a.entries' ↦*□ ents ∗
      "Hcap" ∷ ownSliceCap raftpb.Entry a.entries' (DFrac.own 1) }}
    (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"maybeAppend"))
      (Val #a)) (Val #committed))
  {{ (lastnewi : w64) (ok : Bool) (ls' : LogState), RET (PairV #lastnewi #ok);
      ownRaftLog l ls' ∗
      ⌜match plogMaybeAppend ls.prev (ls.sents ++ ls.uents) a.prev' ents with
        | none => ok = false ∧ lastnewi = W64 0 ∧ ls' = ls
        | some (lni, es') =>
            ok = true ∧ lastnewi = lni ∧
            ls'.prev = ls.prev ∧
            ls'.sents ++ ls'.uents = es' ∧
            ls'.applied = ls.applied ∧
            ls'.committed =
              plogCommitTo ls.committed
                (if uint.Z committed < uint.Z lni then committed else lni) ∧
            ls'.applying = ls.applying ∧ ls'.snap = ls.snap ∧
            ls'.unpersisted = ls.unpersisted ∧ ls'.stored = ls.stored ∧
            ls'.storage = ls.storage⌝ ∗
      -- (2026-10-10) entries still to be handed out stay so (`NGhost.unst`)
      ⌜ls'.snap = ls.snap ∧ (nextUnstable ls ≠ [] → nextUnstable ls' ≠ [])⌝ }}

end spec

end EtcdGrove
end Perennial
