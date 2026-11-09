/- Port of election_proof/proof_traceBecomeCandidate.v. -/
module

public import Spec.go_etcd_io.raft.v3.traceBecomeCandidate
public import Spec.go_etcd_io.raft.v3.traceNodeEvent

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem traceBecomeCandidate.wp_proof
    (wp_traceNodeEvent : traceNodeEvent.spec (GF := GF) (hG := hG)) :
    traceBecomeCandidate.spec (GF := GF) (hG := hG) := by
  intro c r id s tl Q
  wp_start as ⟨#Htl, Hown, Hfire⟩
  wp_auto
  wp_apply wp_traceNodeEvent (W64 1) c r id s tl Q (by decide) $$ [$Htl $Hown $Hfire] as HR
  iapply HΦ $$ HR

end proof

end EtcdGrove
end Perennial
