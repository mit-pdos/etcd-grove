/-
`newStreamHandler` (rafthttp stage 6c). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newStreamHandler

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.newStreamHandler.wp_proof :
    rafthttp.newStreamHandler.spec (GF := GF) (hG := hG) := by
  intro Rh a γd Rs t gi r id cid lg Hlg Hown
  wp_start as ⟨#Hlgf, #Hid, #Hraft, #HGet, #HAddR, #HPfx⟩
  wp_auto
  rw [_root_.decide_eq_false Hlg]
  ipersist «$r0»
  wp_auto
  iapply HΦ
  iexists «$r0_ptr»
  isplitr
  · ipureintro; rfl
  iunfold streamHandlerOk
  iexists _, gi
  iframe #
  ipureintro; exact ⟨Hlg, Hown, rfl⟩

end proof

end EtcdGrove
end Perennial
