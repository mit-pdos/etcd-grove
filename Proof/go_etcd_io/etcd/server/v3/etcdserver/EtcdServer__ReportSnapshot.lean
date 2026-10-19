/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__ReportSnapshot.lean`. Lean-first (no Rocq
counterpart); D21 stage M2 (2026-10-19).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ReportSnapshot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.ReportSnapshot.wp_proof :
    EtcdServer.ReportSnapshot.spec (GF := GF) (hG := hG) := by
  intro γn s id x stt
  wp_start as #Hok
  iunfold srvProcOk at Hok
  icases Hok with ⟨%l, %c, %st, %γ, #Hlg, %Hlgnn, #Hid, %Hγid, #Hcl, #Hrc, #Hst, %Hstnn, #Hn,
    #Hsi, %HN⟩
  iunfold rnStepIfc at Hsi
  icases Hsi with ⟨%ni, %Hni, -, -, #HRU⟩
  have Hni' : ni = ⟨go.GoType.PointerType node.ty, #γ.nl⟩ :=
    (GoInterface.ok.inj Hni).symm
  subst Hni'
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"ReportSnapshot")]
  wp_pures
  rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"ReportSnapshot")]
  wp_pures
  (try wp_auto)
  wp_apply HRU
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
