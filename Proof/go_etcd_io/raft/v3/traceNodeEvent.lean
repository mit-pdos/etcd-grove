/-
Lean-first (no Rocq counterpart): the proof of `traceNodeEvent` (`Spec/go_etcd_io/raft/v3/traceNodeEvent.lean`).
-/
module

public import Spec.go_etcd_io.raft.v3.traceNodeEvent

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem traceNodeEvent.wp_proof
    (wp_traceEvent : traceEvent.spec (GF := GF) (hG := hG)) :
    traceNodeEvent.spec (GF := GF) (hG := hG) := by
  intro evt r tl
  wp_start as ⟨#Htl, %Hok⟩
  wp_auto
  wp_apply wp_traceEvent $$ [$Htl]
  · ipureintro; exact Hok
  iapply HΦ
  ipureintro; trivial

end proof

end EtcdGrove
end Perennial
