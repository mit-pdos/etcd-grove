/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/interpretWatchError.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.interpretWatchError
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewResourceExpired

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

theorem interpretWatchError.wp_proof
    (wp_NewResourceExpired : apierrors.NewResourceExpired.spec (GF := GF) (hG := hG)) :
    interpretWatchError.spec (GF := GF) (hG := hG) := by
  intro err
  unfold kErrOk
  wp_start as ⟨%e, %He, %Heq, #Hstr, %Hfmt, #Hcode, #Hgrpc, #Has, #Hst⟩
  subst He
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hri with ⟨-, ⟨%ce, #Hce, -, -, -, %Hcety⟩, -⟩
  obtain ⟨y, hy⟩ := Hcety
  cases ce
  cases hy
  ihave #Pae : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
  · iPkgInit
  wp_auto
  wp_bind (ite _ _ _)
  iapply wp_kErrOk_eq_etcd e y _ Heq.2
  iintro %b
  wp_auto
  cases b
  case true =>
    wp_auto
    wp_apply wp_NewResourceExpired $$ [] as %p ⟨%st, Hp, %Hst⟩
    (try wp_auto)
    iapply HΦ
    iright
    iexists p, st
    iframe
    ipureintro
    exact ⟨rfl, Hst.1⟩
  wp_auto
  wp_bind (App (App (Val #(functions _root_.Perennial.errors.As [])) _) _)
  iapply Has $$ corruptobjDeletedErr
  inext
  iintro -
  wp_auto
  iapply HΦ
  ileft
  ipureintro
  rfl

end proof

end k8s
end EtcdGrove
end Perennial
