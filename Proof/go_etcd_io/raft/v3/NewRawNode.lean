/- Lean-first (no Rocq counterpart).

raft v3.7 (2026-10-16, stage R5): `newRaft` takes `InitialState` in D7's shape (the conf state a
record `csm`); `prevHardSt` is `r.hardState()`, a fresh read-only hard state (`hsRO`), which
`ownRawNode_intro` takes. Since 2026-10-16 (stage R8b) the result is the node open
(`rawNodeFresh`): `RestartNode` closes it with the ghost state, in either mode (the closing was
here until then). -/
module

public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Spec.go_etcd_io.raft.v3.raft__softState
public import Spec.go_etcd_io.raft.v3.raft__hardState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `newRaft` on the empty storage is the protocol's initial state (`newRaft_post_init`);
the new `RawNode` holds it with nothing handed out. -/
theorem NewRawNode.wp_proof
    (wp_newRaft : newRaft.spec (GF := GF) (hG := hG))
    (wp_softState : raft.softState.spec (GF := GF) (hG := hG))
    (wp_hardState : raft.hardState.spec (GF := GF) (hG := hG)) :
    NewRawNode.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

end proof

end EtcdGrove
end Perennial
