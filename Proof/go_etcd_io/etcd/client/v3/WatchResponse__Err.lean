/-
Proof of `Spec/WatchResponse__Err.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__Err
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error
public import Spec.google_golang_org.grpc.status.Error
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

-- Loads from the fractional response: the field-store `AccessStrict` instances (which need
-- `DFrac.own 1`) are found first and the search does not backtrack.
attribute [-instance] go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_Header
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_Events
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_CompactRevision
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_Canceled
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_Created
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_closeErr
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_CancelReason

theorem WatchResponse.Err.wp_proof
    (wp_rpctypes_Error : rpctypes.Error.spec (GF := GF) (hG := hG))
    (wp_status_Error : status.Error.spec (GF := GF) (hG := hG)) :
    WatchResponse.Err.spec (GF := GF) (hG := hG) := by
  intro wr resp dq
  wp_start as Hwr
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave Hri : (rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hri with ⟨⟨%eFR, #HeFR⟩, ⟨%eCP, #HeCP, #HeCPs⟩, #HFR⟩
  ihave #HeFRs := HFR $$ HeFR
  wp_auto
  cases hce : resp.closeErr' with
  | ok i =>
    wp_auto
    wp_apply wp_rpctypes_Error as %err' ⟨%Hne, #Hw⟩
    · ipureintro; simp [hce]
    iapply HΦ
    iframe
    isplitl []
    · ipureintro; simp [Hne]
    rw [hce]; iexact Hw
  | nil =>
    wp_auto
    wp_if_destruct
    · -- compacted
      iapply HΦ
      iframe
      isplitl []
      · ipureintro; simp_all
      imodintro; iintro -; iapply errStrOk_ok; iexact HeCPs
    cases hca : resp.Canceled'
    · wp_auto
      iapply HΦ
      iframe
      isplitl []
      · ipureintro; simp_all
      imodintro; iintro -; iapply errStrOk_nil
    · wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      wp_if_destruct
      · -- `rpctypes.ErrFutureRev`
        iapply HΦ
        iframe
        isplitl []
        · ipureintro; simp
        imodintro; iintro -; iapply errStrOk_ok; iexact HeFRs
      · -- a cancel reason: `rpctypes.Error(status.Error(codes.FailedPrecondition, reason))`
        wp_apply wp_status_Error as %e1 ⟨%He1, #He1s⟩
        · ipureintro
          simp only [google_golang_org.grpc.codes.OK]
          exact fun h => absurd (go.intoVal_inj h) (by decide)
        wp_apply wp_rpctypes_Error as %e2 ⟨%He2, #Hw⟩
        · ipureintro; exact He1
        iapply HΦ
        iframe
        isplitl []
        · ipureintro; simp [He2]
        imodintro; iintro -; iapply Hw; iexact He1s

end proof

end EtcdGrove
end Perennial
