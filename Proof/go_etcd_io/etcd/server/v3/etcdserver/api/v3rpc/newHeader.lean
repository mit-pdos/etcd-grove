/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newHeader

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.newHeader.wp_proof : v3rpc.newHeader.spec (GF := GF) (hG := hG) := by
  intro s A
  wp_start as #Hkv
  iapply wp_fupd
  ihave #Hkv' := Hkv
  iunfold v3rpc.raftKV at Hkv'
  icases Hkv' with ⟨-, -, -, -, #HG⟩
  iunfold v3rpc.kvGetOk at HG
  icases HG with ⟨#HKV, #HCl, #HMid, #Hrs⟩
  wp_auto
  wp_apply HCl as %c ⟨%ci, %Hci, #HID⟩
  subst Hci
  wp_auto
  wp_apply HID as %cid _
  wp_apply HMid as %mid _
  ipersist s
  simp only [recv_eq_func_mk]
  wp_auto
  imodintro
  iapply HΦ
  iexists cid, mid
  iunfold v3rpc.hdrValIs
  iframe #
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  imodintro
  iintro %Φ' HR HΦ'
  wp_auto
  wp_apply HKV as %kv ⟨%ki, %Hki, #HRev⟩
  subst Hki
  wp_auto
  wp_apply HRev $$ HR as %rv HR
  iapply HΦ'
  iexact HR

end proof

end EtcdGrove
end Perennial
