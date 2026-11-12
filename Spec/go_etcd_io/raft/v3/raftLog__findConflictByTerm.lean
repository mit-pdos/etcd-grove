/-
Port of `election_proof/spec_raftLog__findConflictByTerm.v` (feb5c73d4).

Lean notes: Rocq's `(#i', #t')` is `PairV #i' #t'`.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `l.findConflictByTerm(index, term)`: a guess `(i', t')` at where our log stops
agreeing with a log whose entry at `index` has term `term`.

Only `i' <= index` is specified (and, 2026-10-19, D21 M3, that the walk stops at or above `1`
when the log's term at `1` is at most `term`), and the log is unchanged. The result is a *hint* --
the `RejectHint`/`LogTerm` of a rejecting `MsgAppResp`, and the leader's next probe --
and the protocol model takes any hint (`Step.appReject` quantifies over it), so
pinning it buys nothing for safety.

The body (`raftLog.findConflictByTerm.impl`, `Code/go_etcd_io/raft/v3.lean`;
Rocq new/code/go_etcd_io/raft/v3.v:681) is

    for ; index > 0; index-- {
        if ourTerm, err := l.term(index); err != nil { return index, 0 }
        else if ourTerm <= term { return index, ourTerm }
    }
    return 0, 0

with no panic; the loop invariant is that the counter has only gone down. `term` is
total, so no premise is needed. -/
abbrev raftLog.findConflictByTerm.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (index term : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"findConflictByTerm"))
      (Val #index)) (Val #term))
  {{ (i' t' : w64), RET (PairV #i' #t');
      ownRaftLog l ls ∗ ⌜uint.Z i' ≤ uint.Z index ∧
        -- (2026-10-19, D21 M3) the walk stops at or above `1` when the log's term at `1`, if it
        -- has one, is at most `term` (a leader's rejection handling in the no-snapshot mode)
        (1 ≤ uint.Z index →
          (∀ t0, plogTermAt ls.prev (ls.sents ++ ls.uents) (W64 1) = some t0 →
            uint.Z t0 ≤ uint.Z term) → 1 ≤ uint.Z i')⌝ }}

end spec

end EtcdGrove
end Perennial
