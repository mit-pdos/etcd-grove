/-
Port of `election_proof/spec_raftLog__append.v` (feb5c73d4).

Lean notes:
* `ents !! 0%nat = Some e0` is `ents[0]? = some e0`; the chained `a < b ≤ c` is
  `a < b ∧ b ≤ c`; `Forall P ents` is `∀ e ∈ ents, P e`.
* `log_adopts`/`log_truncate_append` (`InvRaftlog.lean`) are `logAdopts`/
  `logTruncateAppend`, `plog_truncate_append` (`Plog.lean`) is `plogTruncateAppend`;
  `DfracDiscarded` is `DFrac.discard`. `logAdopts` is a `Bool`, so the two `if`s are
  on it directly, their branches written as `iprop(…)`.
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

/-- `l.append(ents)`: splice a batch into the log, truncating whatever it overwrites,
and return the new last index (`raftLog.append.impl`,
`Code/go_etcd_io/raft/v3.lean`; Rocq new/code/go_etcd_io/raft/v3.v:599).

    if len(ents) == 0 { return l.lastIndex() }
    if after := ents[0].Index - 1; after < l.committed {
        l.logger.Panicf("after(%d) is out of range [committed(%d)]", …)
    }
    l.unstable.truncateAndAppend(ents)
    return l.lastIndex()

**Widened 2026-10-01** from "the batch continues the log" to any batch starting inside
or right after it, which is what `maybeAppend` needs (it appends the suffix of a
`MsgApp` from the first conflict on). The new state is `logTruncateAppend ls ents`
(`InvRaftlog.lean`); its entries are `plogTruncateAppend prev (sents ++ uents) ents`
(`Plog.lean`), which the postcondition states. A batch starting in the stable part
shrinks the visible stable part `sents` and becomes the whole unstable suffix (the
shadowed storage tail stays in `Storage`).

Premises (for a non-empty batch, `e0 = ents[0]`):

- `committed < e0.Index <= lastIndex() + 1`: the upper bound is `truncateAndAppend`'s
  (a gap would be a `Panicf` in `u.slice`); the lower bound makes the `Panicf` above
  dead (`after = e0.Index - 1 >= committed`) -- the protocol fact "an accepted `MsgApp`
  never rewrites a committed entry" (`raft-replication-model.md`, "Protocol facts the
  code needs") -- and keeps `committed` inside the new log;
- contiguous indices from `e0.Index` and `e0.Index + |ents| < 2^64`: the new log is
  `LogIndicesOk` and does not wrap. `ownRaftLog` cannot carry a bound that survives a
  longer log (`InvRaftlog.lean`), so the caller supplies it. (Until 2026-10-13 also: no
  configuration change in the batch, `HnoConfChange`'s scope.)

**The batch**: lent and returned unless `logAdopts ls ents` -- the batch starts at or
below the unstable offset without continuing the suffix -- in which case
`truncateAndAppend` adopts the slice itself as `u.entries`, and the caller hands it
over read-only with its capacity (`Spec/unstable__truncateAndAppend.lean`).
`appendEntry`'s batch continues the log, so for it `logAdopts` is `false`
(`logTruncateAppend_cont`). -/
abbrev raftLog.append.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (ents : List raftpb.Entry) (es : GoSlice) (dq : DFrac),
  (∀ e0, ents[0]? = some e0 →
     (uint.Z ls.committed < uint.Z e0.Index' ∧
      uint.Z e0.Index' ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
        + (ls.uents.length : Int) + 1) ∧
     (∀ (k : Nat) e, ents[k]? = some e →
        uint.Z e.Index' = uint.Z e0.Index' + (k : Int)) ∧
     uint.Z e0.Index' + (ents.length : Int) < 2^64) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls ∗
      "Hes" ∷ es ↦*{dq} ents ∗
      "Hadopt" ∷ (if logAdopts ls ents
                  then iprop(⌜dq = DFrac.discard⌝ ∗ ownSliceCap raftpb.Entry es (DFrac.own 1))
                  else iprop(True)) }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"append")) (Val #es))
  {{ (li : w64), RET #li;
      ownRaftLog l (logTruncateAppend ls ents) ∗
      (if logAdopts ls ents then iprop(True) else iprop(es ↦*{dq} ents)) ∗
      ⌜(logTruncateAppend ls ents).sents ++ (logTruncateAppend ls ents).uents
          = plogTruncateAppend ls.prev (ls.sents ++ ls.uents) ents ∧
        uint.Z li = uint.Z ls.prev.index'
                    + ((logTruncateAppend ls ents).sents.length : Int)
                    + ((logTruncateAppend ls ents).uents.length : Int)⌝ }}

end spec

end EtcdGrove
end Perennial
