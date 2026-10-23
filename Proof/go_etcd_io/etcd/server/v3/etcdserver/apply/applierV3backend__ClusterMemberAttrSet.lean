/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__ClusterMemberAttrSet

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]


theorem apply.applierV3backend.ClusterMemberAttrSet.wp_proof :
    apply.applierV3backend.ClusterMemberAttrSet.spec (GF := GF) (hG := hG) := by
  intro E p r v3 log Pre Q Post mm rs
  wp_start as ⟨#Hb, #Hr, Hpre, Hwt, HRO⟩
  iunfold apply.mPreV at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  icases Hard with ⟨Hard, Hwo⟩
  icases mvcc.writerOwn_rt _ $$ Hwo with ⟨Hrt, Hrdb⟩
  iunfold apply.backendIs at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨-, -, -, -, -, -, #Hc, -⟩
  iunfold apply.isCluster at Hc
  icases Hc with ⟨%Hcnn, -, -, -, #HUA, -⟩
  iunfold apply.memberAttrSetIs at Hr
  icases Hr with ⟨%Hrnn, %a, %sl, #Hid, #Ha, %Hann, #Hname, #Hurls, #Hsl⟩
  iStructNamed Hopts
  wp_auto
  wp_apply HUA $$ [$Hcs $Hwt $Hrt $HRO] as ⟨HPP, Hrt, HRO⟩
  · iframe Hsl
  ihave Hwo := Hrdb $$ Hrt
  ihave Hkv : apply.kvOwn E log $$ [Hrd Hsw Hknown Hard Hwo]
  · iunfold apply.kvOwn; iframe
  iapply HΦ
  iunfold apply.mPostV
  iframe HRO
  iframe

end proof

end EtcdGrove
end Perennial
