/-
Port of election_proof/proof_traceCommit.v.
-/
module

public import Spec.go_etcd_io.raft.v3.traceCommit
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

theorem traceCommit.wp_proof
    (wp_traceNodeEvent : traceNodeEvent.spec (GF := GF) (hG := hG)) :
    traceCommit.spec (GF := GF) (hG := hG) := by
  intro r tl
  wp_start as ⟨#Htl, %Hok⟩
  wp_auto
  wp_apply wp_traceNodeEvent $$ [$Htl]
  · ipureintro; exact Hok
  iapply HΦ
  ipureintro; trivial

end proof

end EtcdGrove
end Perennial
