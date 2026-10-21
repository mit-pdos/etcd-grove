/-
Proof of `Spec/go_etcd_io/etcd/client/v3/lessor__Revoke.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__Revoke
public import Spec.go_etcd_io.etcd.client.v3.retryLeaseClient__LeaseRevoke
public import Spec.go_etcd_io.etcd.client.v3.ContextError

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 0 in
theorem lessor.Revoke.wp_proof
    (wp_retry : retryLeaseClient.LeaseRevoke.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    lessor.Revoke.spec (GF := GF) (hG := hG) := by
  intro l addr Spec Q ctx cd id
  wp_start as ⟨#Hrem, #Hrpc, #Hpre, #Hctx, #Hce⟩
  iunfold lessorRemoteAt at Hrem
  icases Hrem with ⟨%rlc, %conn, %sl, #Hremote, #Hrlc, #Hconn, #Hcopts, #Hco⟩
  iunfold callOptsAt at Hco
  icases Hco with ⟨%vs, #Hsl, %Hcap, #Hok, -⟩
  wp_auto
  wp_apply wp_retry rlc conn addr Spec Q ctx cd _ _ sl vs $$ [«$r0»] as %resp %err ⟨-, Hres⟩
  · iframe #
    iframe
    simp only
    iframe #
    ipureintro; exact Hcap
  iunfold leaseRevokeCallOut at Hres
  icases Hres with (⟨%Herr, %m, #Hm, HQ⟩ | ⟨%Herr, #Hse⟩)
  · subst Herr
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists m
    iframe #
    iframe
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      wp_apply wp_ContextError ctx cd (GoInterface.ok ei) $$ [$Hse] as %err' ⟨%Herr', #Hse'⟩
      · iframe #; ipureintro; exact fun _ => Hce'
      iapply HΦ
      iright
      iframe #
      ipureintro
      exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, rfl⟩

end proof

end EtcdGrove
end Perennial
