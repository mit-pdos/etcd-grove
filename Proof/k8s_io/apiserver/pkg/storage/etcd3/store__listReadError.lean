/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__listReadError.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__listReadError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.interpretListError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__GetCurrentResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.NewTooLargeResourceVersionError
public import Spec.errors.IsStatusErr

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
variable [errors_sem : _root_.Perennial.errors.Assumptions]

theorem store.listReadError.wp_proof
    (wp_interpretListError : interpretListError.spec (GF := GF) (hG := hG))
    (wp_GetCRV : store.GetCurrentResourceVersion.spec (GF := GF) (hG := hG))
    (wp_TooLarge : storage.NewTooLargeResourceVersionError.spec (GF := GF) (hG := hG))
    (wp_Is : errors.IsStatusErr.spec (GF := GF) (hG := hG)) :
    store.listReadError.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c ci cd err withRev ck kp Q hk
  obtain ⟨k, hk, hkl⟩ := hk
  wp_start as ⟨#Hst, #Hctx, #Hce, #Herr⟩
  ihave #Prt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave #Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Prt
  icases Hri with ⟨⟨%eFR, #HeFR, %HdFR, %HtFR⟩, -⟩
  obtain ⟨x, hx⟩ := HtFR
  iunfold readErrIs at Herr
  icases Herr with ⟨#Hke, #Hfut⟩
  ihave #Hke' := Hke
  iunfold kClientErr at Hke'
  icases Hke' with ⟨%hce, #Hse, -⟩
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  wp_auto
  sorry

end proof

end k8s
end EtcdGrove
end Perennial
