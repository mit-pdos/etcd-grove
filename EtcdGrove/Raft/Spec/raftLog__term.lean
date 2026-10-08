/-
Port of election_proof/spec_raftLog__term.v (feb5c73d4).

Lean notes:
* Rocq's `(#t, #err)` is `PairV #t #err`; the chained `a ≤ b ≤ c` is a conjunction.
  `global_addr raft.ErrCompacted` is `globalAddr ErrCompacted`; `plog_term_at` is
  `plogTermAt` (`Plog.lean`).
* The reference `raftLog__termⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:1063` is to the
  Lean generated code `raftLog.term.impl`.
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

/-- `l.term(i)`: the term of index `i`.

**Total** (changed 2026-09-21). It used to take
`prev.index ≤ i ≤ prev.index + |sents| + |uents|` as a premise and conclude
`err = interface.nil`. `maybeSendAppend` cannot supply that premise -- it calls
`r.raftLog.term(pr.Next - 1)` and nothing in `ownProgress` bounds a peer's `Next`
against the log -- and the Go code does not assume it either: it branches on
`err != nil` into `maybeSendSnapshot`. So the premise moved into the conclusion.

That the triple can be total is a fact about the body (`raftLog.term.impl`,
`EtcdRaft/Code/go_etcd_io/raft/v3.lean`): it returns `(0, ErrCompacted)` for
`i+1 < firstIndex` and `(0, ErrUnavailable)` for `i > lastIndex`, and inside the range
it asks `unstable.maybeTerm` and then `Storage.Term`, whose error path -- the only
`panic` in the function -- is excluded by `isStorage`'s `HTerm`. Both `firstIndex` and
`lastIndex` are called on the log itself, which is why both are postulates of this
collection along with `unstable.maybeTerm`.

The conclusion is an **iff**: the error is `nil` exactly on the range the old premise
described. Both halves are used. `lastEntryID` calls `term` at `lastIndex` and needs
`←` to kill its `Panicf`. `maybeSendAppend` needs `→`: having tested `err != nil` and
fallen through, it calls `r.raftLog.entries(pr.Next, …)`, whose premise is
`prev.index + 1 ≤ pr.Next` -- and the only thing that establishes it is that
`term(pr.Next - 1)` succeeded. (The `-1` does not spoil it: at `pr.Next = 0` the
argument is `2^64 - 1`, which `Hnowrap` puts outside the range, so `pr.Next ≠ 0` and
the subtraction does not wrap.)

**Which error** (since 2026-10-01): a non-`nil` error is the value of one of the two
globals `ErrCompacted`, `ErrUnavailable` -- the last conjunct, stated by the globals'
(persistent) points-tos since their values are only known through `is_initialized`.
`handleAppendEntries` needs it: its reject path passes `term(m.Index)` straight to
`zeroTermOnOutOfBounds`, which `Panicf`s on any other error, and `m.Index` may well be
past the last index there. Which of the two goes with which side of the range is true
but not stated; nothing needs it.

**The returned term is pinned** (since 2026-10-01): on the `nil` branch it is
`plogTermAt prev (sents ++ uents) i` (`Plog.lean`), the term of the log the protocol
model sees. Log replication needs it -- `matchTerm`, and through it `findConflict`,
`maybeAppend` and `maybeCommit`, compare it. In the unstable window it comes from
`unstable.maybeTerm`'s widened spec, below it from `isStorage`'s `HTerm`
(`termAt prev stored i`), which agrees with `plogTermAt` on the visible stable prefix
`sents` (`Proof/raftLog__term.lean`). Until then the term was unspecified and nothing
on the election path read it. -/
abbrev raftLog.term.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"term")) (Val #i))
  {{ (t : w64) (err : GoInterface), RET (PairV #t #err);
      ownRaftLog l ls ∗
      ⌜err = interface.nil ↔
        (uint.Z ls.prev.index' ≤ uint.Z i ∧
         uint.Z i ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
           + (ls.uents.length : Int))⌝ ∗
      ⌜err = interface.nil →
        plogTermAt ls.prev (ls.sents ++ ls.uents) i = some t⌝ ∗
      (⌜err = interface.nil⌝ ∨ globalAddr ErrCompacted ↦□ err ∨
       globalAddr ErrUnavailable ↦□ err) }}

end spec

end EtcdGrove
end Perennial
