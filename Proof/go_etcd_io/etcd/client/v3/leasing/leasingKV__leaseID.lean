/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__leaseID.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__leaseID
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Lease
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.leaseID.wp_proof
    (hLease : EtcdGrove.concurrency.Session.Lease.spec (GF := GF) (hG := hG)) :
    leasingKV.leaseID.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx
  wp_start as ⟨#Hlkv, Hrd, #Hready⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold lkvReader leaseCacheReader
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  icases leaseCacheInv_open $$ HP with ⟨%st, Hown, HX, Hinst, #Hfacts, %Hwf, Hclose⟩
  icases leasingX_session_ready lkv γ st _ $$ [$Hready $HX] with ⟨%s, Hs, %Hsnn, #Hso, HXback⟩
  unfold sessionOk
  simp only [Hsnn, ↓reduceIte]
  icases Hso with ⟨%γs, %cl, %id, #Hsess, -⟩
  wp_auto
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency $$ []
  · iPkgInit
  wp_apply hLease s γs cl id $$ [$Hcpkg $Hsess]
  ihave #Hsess' := Hsess
  unfold concurrency.isSession
  icases Hsess' with ⟨%ops, %o, %octx, %ocs, %ctx, %cs, %cancel, %donec, -, -, -, -, -, -, -, %Ho, -⟩
  ihave HX := HXback $$ Hs
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hown HX Hinst] as Hrd
  · inext
    iapply Hclose $$ Hown HX Hinst
  iapply HΦ
  iframe
  ipureintro; exact Ho.2

end proof

end leasing
end EtcdGrove
end Perennial
