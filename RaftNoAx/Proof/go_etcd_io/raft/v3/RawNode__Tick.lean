-- The copy for the part `RaftNoAx/` of `Proof/go_etcd_io/raft/v3/RawNode__Tick.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

(#33 S4, P-raft-3) The proof is the strengthened triple's, `RawNode.Tick.wp_absProof`
(`RawNode__TickAbs.lean`, where this file's proof moved, over `ownRawNodeAt`); the old spec is its
corollary (`RawNode.Tick.spec_of_abs`, `RawNodeSpecOfAbs.lean`). One proof.

Until then: both modes (2026-11-12, trace-check cleanup, step-4 review F3), the untraced proof (the
ticks' untraced instances) and the traced one (slice 26n: the ticks' traced instances at the
capability `rnTrace` holds, which comes back idle at the end state), after a common prefix. -/
module

public import RaftNoAx.Spec.go_etcd_io.raft.v3.RawNode__Tick
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raft__tickHeartbeat
public import RaftNoAx.Proof.go_etcd_io.raft.v3.RawNode__TickAbs
public import RaftNoAx.Proof.go_etcd_io.raft.v3.RawNodeSpecOfAbs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.tick` is one of the two tick functions; either one's `TickStep` keeps `ownRawNode` but for
the term (`RawNode.Tick.wp_absProof` outside the scope). -/
theorem RawNode.Tick.wp_proof
    (wp_tickElection : raft.tickElection.spec (GF := GF) (hG := hG))
    (wp_tickHeartbeat : raft.tickHeartbeat.spec (GF := GF) (hG := hG)) :
    RawNode.Tick.spec (GF := GF) (hG := hG) :=
  RawNode.Tick.spec_of_abs (RawNode.Tick.wp_absProof wp_tickElection wp_tickHeartbeat)

end proof

end EtcdGrove
end Perennial
