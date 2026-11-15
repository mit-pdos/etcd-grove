/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__prepareObjs.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__prepareObjs
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.decodeObj
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__acceptAll

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

theorem watchChan.prepareObjs.wp_proof
    (wp_decodeObj : decodeObj.spec (GF := GF) (hG := hG))
    (wp_acceptAll : watchChan.acceptAll.spec (GF := GF) (hG := hG)) :
    watchChan.prepareObjs.spec (GF := GF) (hG := hG) := by
  intro Obj S W codec vi ti wc wp ctx p sel emp ep x σ r hdec
  wp_start as ⟨#Hw, #Hctx, #Hp, #Hcodec, #Hvi, #Hti, #Hsel, #Htr, #Hver, #Hwc, #Hep, #Hx⟩
  ihave #Htr' := Htr
  iunfold transformerOk at Htr'
  icases Htr' with ⟨#Hfrom, -⟩
  ihave #Hep' := Hep
  iStructNamed Hep'
  cases r with
  | bm rr a =>
    unfold kEvIs
    icases Hx with %Hx
    obtain ⟨-, Hpn, -⟩ := Hx
    wp_auto
    rw [Hpn]
    wp_auto
    iapply HΦ
    simp only [kCurObj, kOldObj, kObjOpt]
    iframe; ipureintro; simp
  | kv v =>
    sorry
  | ev e =>
    sorry

end proof

end k8s
end EtcdGrove
end Perennial
