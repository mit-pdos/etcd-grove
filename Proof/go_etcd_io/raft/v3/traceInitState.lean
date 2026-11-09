/- Port of election_proof/proof_traceInitState.v. -/
module

public import Spec.go_etcd_io.raft.v3.traceInitState
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

theorem traceInitState.wp_proof
    (wp_traceNodeEvent : traceNodeEvent.spec (GF := GF) (hG := hG)) :
    traceInitState.spec (GF := GF) (hG := hG) := by
  intro c r id s tl Q
  wp_start as ⟨#Htl, Hown, Hfire⟩
  cases tl with
  | nil =>
    wp_auto
    iapply HΦ
    iframe Hown
    iapply traceFire_nil $$ Hfire
  | ok l =>
    wp_auto
    wp_apply wp_traceNodeEvent (W64 0) c r id s _ Q (by decide) $$ [$Htl $Hown $Hfire] as HR
    iapply HΦ $$ HR

end proof

end EtcdGrove
end Perennial
