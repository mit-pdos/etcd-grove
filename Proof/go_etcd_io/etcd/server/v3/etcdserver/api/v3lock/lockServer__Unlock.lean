/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3lock/lockServer__Unlock.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.lockServer__Unlock

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3lock

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency concurrency
  _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Assumptions]

theorem lockServer.Unlock.wp_proof : lockServer.Unlock.spec (GF := GF) (hG := hG) := by
  intro ls c req ksl key ctx cs
  wp_start as ⟨#Hls, #Hok, #Hkf, #Hks, #Hctx⟩
  iunfold isLockServer at Hls
  iunfold unlockKVOk at Hok
  icases Hok with ⟨%kv, #Hkv, #HDel⟩
  wp_auto
  wp_apply wp_bytes_to_string ksl key DFrac.discard $$ [$Hks] as -
  (try wp_auto)
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty)]
  (try wp_auto)
  wp_apply HDel $$ %ctx %cs %key [$Hctx] as %resp %err Hres
  icases Hres with (%Herr | ⟨%Herr, %hdr, #Hhdr, #Hdr⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok e =>
      (try wp_auto)
      iapply HΦ
      iright
      ipureintro
      exact ⟨rfl, Herr⟩
  · subst Herr
    (try wp_auto)
    wp_alloc r as Hr
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists hdr, _
    iframe Hr Hdr
    ipureintro
    rfl

end proof

end v3lock
end EtcdGrove
end Perennial
