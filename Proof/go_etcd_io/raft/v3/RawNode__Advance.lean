/-
Port of `election_proof/proof_RawNode__Advance.v` (857d09190).

(2026-11-12, trace-check step 4, `hAdv`) **The instance of the proof for both modes**: the proof is
`RawNode.Advance.tracedSpec_proof` (`TracedRawNodeAdvance.lean`, where this file's proof moved, with its
lemmas), of `RawNode.Advance.tracedSpec` (`TracedRunSpecs.lean`); `RawNode.Advance.spec` is its untraced
instance (`RawNode.Advance.spec_of_tracedSpec`). One proof; this statement unchanged.
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Advance
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Proof.go_etcd_io.raft.v3.TracedRawNodeAdvance

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

theorem RawNode.Advance.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.Advance.spec (GF := GF) (hG := hG) :=
  RawNode.Advance.spec_of_tracedSpec (RawNode.Advance.tracedSpec_proof wp_raft_Step)

end proof

end EtcdGrove
end Perennial
