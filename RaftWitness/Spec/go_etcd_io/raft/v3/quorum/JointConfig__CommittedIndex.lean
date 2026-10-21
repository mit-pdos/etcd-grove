/- Port of election_proof/spec_JointConfig__CommittedIndex.v (feb5c73d4); general since
2026-10-13 (reconfiguration stage A1), Lean-first. -/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvTrackerC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `c.CommittedIndex(l)` for the joint config (`quorum.JointConfig.CommittedIndex.impl`,
`Code/go_etcd_io/raft/v3/quorum.lean`; joint.go:50):

    idx0 := c[0].CommittedIndex(l)
    idx1 := c[1].CommittedIndex(l)
    if idx0 < idx1 { return idx0 }               // exit 1
    return idx1                                  // exit 2

No panic. Calls: `MajorityConfig.CommittedIndex` twice; the indexer's `AckedIndex` is
reached from inside it, through the interface, by the caller-supplied contract
`isAckedIndexer` (`InvTracker.lean`) -- the indexer is arbitrary, with the resource `P`
it needs, which comes back.

**General since 2026-10-13** (reconfiguration stage A1): the receiver is any `*JointConfig`
`c` (read at any fraction; a value receiver), its halves `v0`, `v1` id sets `nil` or maps
(`ownIdsetQ`). The result is `JCommittedIdx`: the smaller of the two halves' answers, each
`MaxUint64` for an empty half and otherwise the quorum index of `(acked v).getD 0` over it
(`MajIdx`, `IsQuorumIndex`); a voter the indexer does not know counts `0`. Until then the
configuration was simple (`a = [m0, nil]`); that statement was
`quorum.JointConfig.CommittedIndex.spec_simple`; it had no caller and is gone (2026-10-17).
(Until 2026-10-04 this was stated for the tracker's receiver and indexer only.) -/
abbrev quorum.JointConfig.CommittedIndex.spec : Prop :=
  ∀ (c : Loc) (dqc : DFrac) (a : quorum.JointConfig) (v0 v1 : Loc) (s0 s1 : GSet w64)
    (l : GoInterface) (P : IProp GF) (acked : w64 → Option w64),
  a.arr = [v0, v1] →
  (GMap.size s0 : Int) ≤ 2 ^ 62 → (GMap.size s1 : Int) ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗
      c ↦{dqc} a ∗ ownIdsetQ v0 (DFrac.own 1) s0 ∗ ownIdsetQ v1 (DFrac.own 1) s1 ∗
      isAckedIndexer l P acked ∗ P }}
    (App (Val (c @!! go.GoType.PointerType quorum.JointConfig.ty @!! go!"CommittedIndex"))
      (Val #l))
  {{ (N : w64), RET #N;
      c ↦{dqc} a ∗ ownIdsetQ v0 (DFrac.own 1) s0 ∗ ownIdsetQ v1 (DFrac.own 1) s1 ∗ P ∗
      ⌜JCommittedIdx s0 s1 (fun v => (acked v).getD (W64 0)) N⌝ }}

end spec

end EtcdGrove
end Perennial
