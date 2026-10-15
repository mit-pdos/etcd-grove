/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewKVServer
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

theorem v3rpc.NewKVServer.wp_proof
    (hNH : v3rpc.newHeader.spec (GF := GF) (hG := hG)) :
    v3rpc.NewKVServer.spec (GF := GF) (hG := hG) := by
  intro s A n
  wp_start as ⟨#Hkv, #Hn⟩
  wp_auto
  wp_apply hNH $$ [] as %hv ⟨%cid, %mid, #Hhv⟩
  · iframe #
  wp_auto
  wp_alloc p as Hp
  ihave %Hpn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  iStructNamed hdr
  ipersist clusterID
  ipersist memberID
  ipersist sg
  ipersist rev
  ipersist kv
  ipersist maxTxnOps
  iunfold v3rpc.hdrValIs at Hhv
  icases Hhv with ⟨%Hhv, #HrevS, #Hrs⟩
  obtain ⟨Hc, Hm, Hsg⟩ := Hhv
  wp_auto
  iapply HΦ
  iexists p, cid, mid
  isplitr
  · ipureintro; rfl
  iunfold v3rpc.kvServerIs
  iunfold v3rpc.hdrIs
  iframe #
  rw [Hc, Hm, Hsg]
  iframe #
  ipureintro; exact Hpn

end proof

end EtcdGrove
end Perennial
