/-
Port of `election_proof/spec_raftLog__term.v`.

Lean notes:
* Rocq's `(#t, #err)` is `PairV #t #err`; the chained `a ≤ b ≤ c` is a conjunction.
* The reference `raftLog__termⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:1063` is to the
  Lean generated code `raftLog.term.impl`.
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

/-- `l.term(i)`: the term of index `i`.

**Total** (changed 2026-09-21). It used to take
`prev.index ≤ i ≤ prev.index + |sents| + |uents|` as a premise and conclude
`err = interface.nil`. `maybeSendAppend` cannot supply that premise -- it calls
`r.raftLog.term(pr.Next - 1)` and nothing in `ownProgress` bounds a peer's `Next`
against the log -- and the Go code does not assume it either: it branches on
`err != nil` into `maybeSendSnapshot`. So the premise moved into the conclusion.

That the triple can be total is a fact about the body (`raftLog.term.impl`,
`Perennial/Code/go_etcd_io/raft/v3.lean`): it returns `(0, ErrCompacted)` for
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

Naming the two errors would also be true (`ErrCompacted` below the boundary,
`ErrUnavailable` above it) but is not statable here without dragging the
`is_initialized` globals into the postcondition, and the iff already tells every caller
which branch it is in.

The returned term is still not specified, and cannot be: in the unstable part of the
range the value comes from `unstable.maybeTerm`, whose triple does not pin it (and
`termAt` describes the *stable* prefix only). Nothing on the election path reads it:
`lastEntryID` only puts it in an `entryID`, and `isUpToDate` comparing the wrong terms
can only make the node decline to vote, which is always protocol-legal;
`maybeSendAppend` puts it in a `MsgApp`'s `LogTerm`, which the abstract message does
not carry. -/
abbrev raftLog.term.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"term")) (Val #i))
  {{ (t : w64) (err : GoInterface), RET (PairV #t #err);
      ownRaftLog l ls ∗
      ⌜err = interface.nil ↔
        (uint.Z ls.prev.index' ≤ uint.Z i ∧
         uint.Z i ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
           + (ls.uents.length : Int))⌝ }}

end spec

end EtcdGrove
end Perennial
