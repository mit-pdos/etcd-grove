/- Port of election_proof/spec_JointConfig__CommittedIndex.v (feb5c73d4). -/
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

/-- `c.CommittedIndex(l)` for the joint config (`quorum.JointConfig.CommittedIndex.impl`,
`Perennial/Code/go_etcd_io/raft/v3/quorum.lean`; joint.go:50):

    idx0 := c[0].CommittedIndex(l)
    idx1 := c[1].CommittedIndex(l)
    if idx0 < idx1 { return idx0 }               // exit 1
    return idx1                                  // exit 2

No panic. Calls: `MajorityConfig.CommittedIndex` twice; the indexer's `AckedIndex` is
reached from inside it, through the interface, by the caller-supplied contract
`isAckedIndexer` (`InvTracker.lean`) -- the indexer is arbitrary, with the resource `P`
it needs, which comes back.

(Until 2026-10-04 this was stated for the tracker's receiver and indexer only, on
`ownTracker`. It is now the general triple, so that `readOnly.maybeAdvance` can use it
with the read-only object as the indexer; `ProgressTracker.Committed`
(`proof_ProgressTracker__Committed.v`) instantiates it at the tracker.)

The receiver is a `*JointConfig` at `c` (a caller holding a struct field passes the
field's location), pointing at a simple configuration: `a = [m0, nil]`, `m0` holding
the voters (`domSet ids`), `c[1]` nil, whose `CommittedIndex` is `MaxUint64` by
convention, so that `min` picks `c[0]`'s answer on both exits. The result is
`MaxUint64` for an empty configuration, and otherwise the quorum index of
`(acked v).getD 0` over the voters (`IsQuorumIndex`); a voter the indexer does not know
counts `0`. The voter map comes back at some `ids'` with the same key set (the callee's
contract). -/
abbrev quorum.JointConfig.CommittedIndex.spec : Prop :=
  ∀ (c : Loc) (a : quorum.JointConfig) (m0 : Loc) (ids : GMap w64 Unit)
    (l : GoInterface) (P : IProp GF) (acked : w64 → Option w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗
      ⌜(GMap.size (domSet ids) : Int) < 2 ^ 63⌝ ∗
      c ↦ a ∗ ⌜a.arr = [m0, map.nil]⌝ ∗ m0 ↦$ ids ∗
      isAckedIndexer l P acked ∗ P }}
    (App (Val (c @!! go.GoType.PointerType quorum.JointConfig.ty @!! go!"CommittedIndex"))
      (Val #l))
  {{ (N : w64), RET #N;
      c ↦ a ∗ (∃ ids' : GMap w64 Unit, ⌜domSet ids' = domSet ids⌝ ∗ m0 ↦$ ids') ∗ P ∗
      ⌜domSet ids = ∅ → N = W64 (2 ^ 64 - 1)⌝ ∗
      ⌜domSet ids ≠ ∅ → IsQuorumIndex (domSet ids) (fun v => (acked v).getD (W64 0)) N⌝ }}

end spec

end EtcdGrove
end Perennial
