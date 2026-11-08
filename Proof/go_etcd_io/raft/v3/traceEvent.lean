/-
Lean-first (no Rocq counterpart): the proof of `traceEvent` (`Spec/go_etcd_io/raft/v3/traceEvent.lean`).
-/
module

public import Spec.go_etcd_io.raft.v3.traceEvent

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

theorem traceEvent.wp_proof : traceEvent.spec (GF := GF) (hG := hG) := by
  intro evt r m prop tl
  wp_start as ⟨#Htl, %Hok⟩
  unfold TraceLoggerOk at Hok; subst Hok
  wp_auto
  iapply HΦ
  ipureintro; trivial

end proof

end EtcdGrove
end Perennial
