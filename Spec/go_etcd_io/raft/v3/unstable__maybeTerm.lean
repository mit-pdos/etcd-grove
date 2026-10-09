/-
Port of election_proof/spec_unstable__maybeTerm.v (feb5c73d4).

Lean notes:
* Rocq's `(#t, #ok)` is `PairV #t #ok`; the chained `a ≤ b < c` is a conjunction;
  `own_snap` is `ownSnap` (`InvRaftlog.lean`); `uents !! Z.to_nat (…)` is
  `uents[(…).toNat]?`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `u.maybeTerm(i)`: the term of index `i` if the unstable suffix covers it, or if `i`
is a pending snapshot's index. `ok` pins down exactly which indices those are, which is
what `raftLog.term` needs in order to decide whether to fall through to `Storage`.
As with the other two `maybe*` methods, on a bare `*unstable`, with the snapshot
pointer as `ownSnap`. The `i >= offset` branch calls `maybeLastIndex`, which is why
that is a postulate here.
When `ok`, `t` is the term of the entry at `i` (since 2026-10-01, for `raftLog.term`'s
widened spec; before, only `ok` was pinned), or the snapshot's term at the snapshot's
index (since 2026-10-02).
The first premise -- a pending snapshot ends right below `offset` -- is what
`unstable.restore` establishes and `ownRaftLog` keeps (`Hoffset` with `sents = []`).
Without it the `i >= offset` branch, after `maybeLastIndex` returned the snapshot's
index, could index `u.entries` out of bounds. -/
abbrev unstable.maybeTerm.spec : Prop :=
  ∀ (u : Loc) (uv : unstable) (uents : List raftpb.Entry) (snap : Option entryID)
    (i : w64),
  (∀ sid, snap = some sid → uint.Z uv.offset' = uint.Z sid.index' + 1) →
  uint.Z uv.offset' + (uents.length : Int) < 2 ^ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u uv uents ∗
      "#Hsnap" ∷ ownSnap uv.snapshot' snap }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"maybeTerm")) (Val #i))
  {{ (t : w64) (ok : Bool), RET (PairV #t #ok);
      ownUnstable u uv uents ∗
      ⌜ok = true ↔ ((uint.Z uv.offset' ≤ uint.Z i ∧
                     uint.Z i < uint.Z uv.offset' + (uents.length : Int)) ∨
                    ∃ sid, snap = some sid ∧ i = sid.index')⌝ ∗
      ⌜ok = true →
        ((uint.Z uv.offset' ≤ uint.Z i ∧
          uint.Z i < uint.Z uv.offset' + (uents.length : Int)) ∧
         ∃ e, uents[(uint.Z i - uint.Z uv.offset').toNat]? = some e ∧ t = e.Term') ∨
        (∃ sid, snap = some sid ∧ i = sid.index' ∧ t = sid.term')⌝ }}

end spec

end EtcdGrove
end Perennial
