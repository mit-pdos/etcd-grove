/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__getList.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getList
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getResourceSizeEstimator
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdRequest
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__List
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__GetAt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.getList.wp_proof
    (wp_kList : kubernetes.Client.List.spec (GF := GF) (hG := hG))
    (wp_kGetAt : kubernetes.Client.GetAt.spec (GF := GF) (hG := hG))
    (wp_RecordEtcdRequest : metrics.RecordEtcdRequest.spec (GF := GF) (hG := hG))
    (wp_rse : store.getResourceSizeEstimator.spec (GF := GF) (hG := hG)) :
    store.getList.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c ci cd kp recur lo Q hkp hct hrev hlim hrc
  wp_start as ⟨#Hst, #Hctx, #Hce, Htt, %htb, HQ⟩
  ihave Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt,
    #Hkc, #Hcl, #Hone, #Hregs, #Hcon, #Hlst⟩
  iunfold storeListOk at Hlst
  icases Hlst with ⟨%lf, %lγ, -, -, -, %Hutf, -⟩
  ihave #Pme : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics $$ []
  · iPkgInit
  ihave #Pti : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Pku : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes $$ []
  · iPkgInit
  ihave #Pcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave Hkc' := Hkc
  iStructNamed Hkc'
  (try wp_auto)
  wp_apply _root_.Perennial.time.wp_Now as %t0 -
  (try wp_auto)
  sorry

end proof

end k8s
end EtcdGrove
end Perennial
