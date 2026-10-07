/-
Port of election_proof/spec_MajorityConfig__CommittedIndex.v (feb5c73d4).

Lean notes:
* `is_pkg_init quorum` is `isPkgInit … pkg_id.go_etcd_io.raft.v3.quorum`;
  `Z.of_nat (size s)` is `(GMap.size s : Int)`; `dom ids` is `domSet ids`;
  `default (W64 0) (acked v)` is `(acked v).getD (W64 0)`; `is_AckedIndexer` and
  `is_quorum_index` are `isAckedIndexer` and `IsQuorumIndex` (`InvTracker.lean`).
* The reference `quorum.MajorityConfig__CommittedIndexⁱᵐᵖˡ,
  new/code/go_etcd_io/raft/v3/quorum.v:355` is to the Lean generated code
  `quorum.MajorityConfig.CommittedIndex.impl`; `spec_slices_Sort.v` is
  `Spec/slices_Sort.lean`.
-/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `c.CommittedIndex(l)` for a *single* majority quorum
(`quorum.MajorityConfig.CommittedIndex.impl`,
`Perennial/Code/go_etcd_io/raft/v3/quorum.lean`; majority.go:121):

    n := len(c)
    if n == 0 { return math.MaxUint64 }           // exit 1
    var stk [7]uint64
    var srt []uint64
    if len(stk) >= n { srt = stk[:n] } else { srt = make([]uint64, n) }
    i := n - 1
    for id := range c {
      if idx, ok := l.AckedIndex(id); ok { srt[i] = uint64(idx); i-- }
    }
    slices.Sort(srt)
    pos := n - (n/2 + 1)
    return Index(srt[pos])                         // exit 2

**Panics**: the two slice accesses `srt[i]` and `srt[pos]` would panic out of range;
neither can. `i` starts at `n-1` and is decremented only after a write, at most once
per voter, so every write is at `n-1-j ≥ 0` with `j` the number of acknowledging voters
seen so far (`j < n` while a voter is still to come). `pos ∈ [0, n)` for `n ≥ 1`. The
`go.int` arithmetic does not wrap under `size s < 2^63`. Calls: `l.AckedIndex`
(dynamic, through the interface: the contract is `isAckedIndexer`, `InvTracker.lean`)
and `slices.Sort` (axiom, `Spec/slices_Sort.lean` -- whose *sortedness* conjunct is
what this function needs).

The receiver is a `*MajorityConfig` at `cref`, exactly as for
`MajorityConfig.VoteResult`: the component is either `map.nil` (then `s = ∅`) or an
owned map with key set `s`. The indexer `l` owns whatever `P` it needs; `P` comes back
unchanged.

The result: `MaxUint64` for an empty config (the convention that makes a nil second
half of a joint config neutral under `min`), and otherwise the **quorum index** of the
per-voter values `(acked v).getD 0` (`IsQuorumIndex`): one of the values, acknowledged
by a quorum of `s`, and the largest such. A voter the indexer does not know counts as
`0` -- that is the zero the `srt` slot keeps. -/
abbrev quorum.MajorityConfig.CommittedIndex.spec : Prop :=
  ∀ (s : GSet w64) (cref mref : Loc) (l : GoInterface) (P : IProp GF)
    (acked : w64 → Option w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗
      ⌜(GMap.size s : Int) < 2 ^ 63⌝ ∗
      cref ↦ mref ∗
      (⌜mref = map.nil ∧ s = ∅⌝ ∨
       ∃ (ids : GMap w64 Unit), ⌜domSet ids = s⌝ ∗ mref ↦$ ids) ∗
      isAckedIndexer l P acked ∗ P }}
    (App (Val (cref @!! go.GoType.PointerType quorum.MajorityConfig.ty
      @!! go!"CommittedIndex")) (Val #l))
  {{ (N : w64), RET #N;
      cref ↦ mref ∗
      (⌜mref = map.nil ∧ s = ∅⌝ ∨
       ∃ (ids : GMap w64 Unit), ⌜domSet ids = s⌝ ∗ mref ↦$ ids) ∗
      P ∗
      ⌜s = ∅ → N = W64 (2 ^ 64 - 1)⌝ ∗
      ⌜s ≠ ∅ → IsQuorumIndex s (fun v => (acked v).getD (W64 0)) N⌝ }}

end spec

end EtcdGrove
end Perennial
