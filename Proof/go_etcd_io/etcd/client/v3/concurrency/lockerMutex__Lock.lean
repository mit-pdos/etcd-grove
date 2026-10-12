/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/lockerMutex__Lock.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.lockerMutex__Lock
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__Lock
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Spec.go_etcd_io.etcd.client.v3.Client__Ctx
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem lockerMutex.Lock.wp_proof (hCl : Session.Client.spec (GF := GF) (hG := hG))
    (hCtx : Client.Ctx.spec (GF := GF) (hG := hG)) (hLock : Mutex.Lock.spec (GF := GF) (hG := hG)) :
    lockerMutex.Lock.spec (GF := GF) (hG := hG) := by
  intro lm m s γ client id pfx st cctx ccs lo
  wp_start as ⟨Hlm, #Hm, Hst, #Hcc, #Hctx, #Hcan, #Hlo, Hstuck⟩
  ihave #Hm' := Hm
  iunfold isMutex at Hm'
  icases Hm' with ⟨#Hms, -, -, #Hsess, -⟩
  wp_auto
  wp_apply hCl s γ client id $$ [$Hpkg $Hsess]
  wp_apply hCtx client (GoInterface.ok cctx) $$ [$Hcc]
  wp_apply hLock m s γ client id pfx st cctx ccs lo $$ [$Hpkg $Hm $Hst $Hctx $Hcan $Hlo]
    as %err Hres
  icases Hres with (⟨%Herr, Hok⟩ | ⟨#Hexp, %st', %R, Hst', -⟩ | ⟨%Hne, %st', Hst'⟩)
  · subst Herr
    wp_auto
    iapply HΦ
    iframe Hlm
    iexact Hok
  · iunfold isPkgErr at Hexp
    icases Hexp with ⟨-, %Hne⟩
    obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    wp_apply wp_panic
    iapply Hstuck $$ %_ %Hne
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    wp_apply wp_panic
    iapply Hstuck $$ %_ %Hne

end proof

end concurrency
end EtcdGrove
end Perennial
