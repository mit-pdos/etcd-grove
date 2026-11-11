/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__DowngradeInfoSet
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]


theorem apply.applierV3backend.DowngradeInfoSet.wp_proof :
    apply.applierV3backend.DowngradeInfoSet.spec (GF := GF) (hG := hG) := by
  intro E p r v3 log Pre Q Post info
  wp_start as ⟨#Hb, ⟨%dm, #Hr⟩, HRW, Hpre⟩
  icases apply.mPreV_split $$ Hpre with ⟨%cr, %B, Hsw, Hcs, Hwt, Hrt, Htie, Hres, Hkv⟩
  iunfold apply.backendIs at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨-, -, -, -, -, -, -, #Hc, -⟩
  iunfold apply.isCluster at Hc
  icases Hc with ⟨%Hcnn, -, -, -, -, #HSD⟩
  iunfold apply.downgradeInfoSetIs at Hr
  icases Hr with ⟨%Hrnn, #Hen, #Hver⟩
  iStructNamed Hopts
  wp_auto
  cases hen : dm.enabled
  all_goals
    wp_auto
    wp_apply HSD $$ [$Hcs $Hwt $Hrt $Htie $d $HRW] as ⟨HPP, Hrt, Htie, HRW⟩
    iapply HΦ
    iapply (apply.mPostV_of _ _ _ _ _ _ _ _ B cr)
    iframe

end proof

end EtcdGrove
end Perennial
