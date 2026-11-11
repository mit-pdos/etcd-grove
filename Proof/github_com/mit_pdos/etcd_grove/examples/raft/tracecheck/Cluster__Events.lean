/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (part 1) (2026-11-11): the proof of
`Cluster__Events`, from the recorder's `Events`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__Events
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder__Events

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

theorem Cluster.Events.wp_proof
    (wp_SyncRecorder_Events : SyncRecorder.Events.spec (GF := GF) (hG := hG)) :
    Cluster.Events.spec (GF := GF) (hG := hG) := by
  intro c γt r Ψ
  wp_start as ⟨#Hrec, #Hr, Hvs⟩
  wp_auto
  wp_apply wp_SyncRecorder_Events γt r Ψ $$ [Hvs] as %sl Hsl
  · iframe Hr Hvs
  iapply HΦ
  iexact Hsl

end proof

end TraceCheck
end EtcdGrove
end Perennial
