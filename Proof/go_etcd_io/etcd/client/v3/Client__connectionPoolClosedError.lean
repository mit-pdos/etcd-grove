/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__connectionPoolClosedError.lean` (PR #21765).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__connectionPoolClosedError

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open go_etcd_io.etcd.cache.v3 (statusErrOk errCellOk)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.connectionPoolClosedError.wp_proof
    (wp_status_Error : status.Error.spec (GF := GF) (hG := hG)) :
    Client.connectionPoolClosedError.spec (GF := GF) (hG := hG) := by
  intro cl dq ci cd st
  wp_start as ⟨Hctx, #Hce, Hst⟩
  ihave #HstPkg : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  iunfold ctxErrClient at Hce
  wp_auto
  wp_bind (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #()))
  iapply Hce $$ %st [Hst]
  · iexact Hst
  inext
  iintro %e He %Hce' #Hse #Hcell
  cases st with
  | Done =>
    icases He with %Hne
    cases e with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe Hctx Hse Hcell
      ipureintro
      exact ⟨by simp, fun _ => Hce'⟩
  | Pending =>
    cases e with
    | nil =>
      wp_auto
      wp_apply wp_status_Error as %err' ⟨%Hne', #Hse'⟩
      · ipureintro
        simp only [google_golang_org.grpc.codes.OK]
        exact fun h => absurd (go.intoVal_inj h) (by decide)
      iapply HΦ
      iframe Hctx Hse'
      ipureintro; exact ⟨Hne', fun h => by cases h⟩
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe Hctx Hse
      ipureintro; simp
  | Unknown =>
    cases e with
    | nil =>
      wp_auto
      wp_apply wp_status_Error as %err' ⟨%Hne', #Hse'⟩
      · ipureintro
        simp only [google_golang_org.grpc.codes.OK]
        exact fun h => absurd (go.intoVal_inj h) (by decide)
      iapply HΦ
      iframe Hctx Hse'
      ipureintro; exact ⟨Hne', fun h => by cases h⟩
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe Hctx Hse
      ipureintro; simp

end proof

end EtcdGrove
end Perennial
