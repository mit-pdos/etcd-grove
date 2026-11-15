/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__getResourceSizeEstimator.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getResourceSizeEstimator

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

theorem store.getResourceSizeEstimator.wp_proof :
    store.getResourceSizeEstimator.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c
  wp_start as ⟨#Hst, Htt⟩
  iunfold isStore at Hst
  icases Hst with ⟨%Hsp, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Hlo⟩
  iunfold storeListOk at Hlo
  icases Hlo with ⟨%f, %γp, -, -, #Hpool, -⟩
  iapply fupd_wp
  imod threadPool.borrow storePoolN γp _ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hpool Htt]
    with ⟨Hown, Hloan⟩
  · iframe #; iframe
  imodintro
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.RWMutex.wp_RLock $$ [$Hown] as ⟨Hrl, HP⟩
  iunfold rseNilR at HP
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HP] as Hown
  · iunfold rseNilR; iexact HP
  iapply fupd_wp
  imod threadPool.giveBack storePoolN γp _ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hpool Hloan Hown]
    with Htt
  · iframe #; iframe
  imodintro
  wp_auto
  iapply HΦ
  iexact Htt

end proof

end k8s
end EtcdGrove
end Perennial
