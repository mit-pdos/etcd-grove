/-
`newPipelineHandler` (rafthttp stage 6c). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newPipelineHandler

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.newPipelineHandler.wp_proof :
    rafthttp.newPipelineHandler.spec (GF := GF) (hG := hG) := by
  intro Rh a γd Rs t r cid lg lid Hlg Hown
  wp_start as ⟨#Hlgf, #Hid, #Hraft, #Harr⟩
  wp_auto
  rw [_root_.decide_eq_false Hlg]
  ipersist «$r0»
  wp_auto
  iapply HΦ
  iexists «$r0_ptr»
  isplitr
  · ipureintro; rfl
  iunfold pipeHandlerOk
  iexists _
  iframe #
  ipureintro; exact ⟨Hlg, Hown⟩

end proof

end EtcdGrove
end Perennial
