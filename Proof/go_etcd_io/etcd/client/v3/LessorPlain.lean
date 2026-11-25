/-
The lease client's `lessor` specs at a plain spec over any connection (auth-lease S4, Freeze §2.2): the
form before the metadata-indexed one, a corollary for the callers that register a plain spec
(`GrpcSpec.md`, `attemptPre_md`, `isGrpcRpcs_md`, `lessorRemoteAt_conn`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__Grant
public import Spec.go_etcd_io.etcd.client.v3.lessor__Revoke
public import Spec.go_etcd_io.etcd.client.v3.lessor__TimeToLive
public import Spec.go_etcd_io.etcd.client.v3.lessor__Leases

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section plain
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `lessor.Grant.spec` at a plain spec over any connection (the form before auth-lease S4's §2.2). -/
abbrev lessor.Grant.specP : Prop :=
  ∀ (l : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse)
    (Q : LeaseGrantRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (ttl : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (lessorRemoteAt l addr ∗
      isGrpcRpcs addr go!"/etcdserverpb.Lease/LeaseGrant" Spec ∗ □ ▷ Spec (ttl, W64 0) Q ∗
      ctxOk ctx cd ∗ ctxErrClient ctx cd) }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Grant"))
      (Val #(GoInterface.ok ctx))) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : LeaseGrantRespM) (h : Loc),
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ResponseHeader" resp ↦□ h ∗
        hdrFull h m.hdr ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"TTL" resp ↦□ m.ttl ∗ Q m) ∨
      (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗
        go_etcd_io.etcd.cache.v3.statusErrOk err)) }}

theorem lessor.Grant.specP_of (h : lessor.Grant.spec (GF := GF) (hG := hG)) :
    lessor.Grant.specP (GF := GF) (hG := hG) := by
  intro l addr Spec Q ctx cd ttl
  iintro %Φ ⟨#Hpkg, Hlt, #Hrem, #Hrpc, #Hpre, #Hctx, Hrest⟩ HΦ
  ihave ⟨%conn, #HremC⟩ := (lessorRemoteAt_conn l addr).1 $$ Hrem
  ihave #HctxO := ctxOk_outgoingC ctx cd $$ Hctx
  iunfold metadata.outgoingCtxOkC at HctxO
  icases HctxO with ⟨%om, #Hom⟩
  iapply (h l conn addr (GrpcSpec.md Spec) Q ctx om cd ttl) $$ [Hlt Hrest] HΦ
  iframe Hlt Hpkg HremC Hom Hctx
  isplitr
  · iapply (isGrpcRpcs_md addr _ Spec).1 $$ Hrpc
  isplitr
  · iintro !>; inext
    unfold attemptPre
    iintro %md -
    simp only [GrpcSpec.md]
    isplitl
    · iexact Hpre
    · iintro !> %_; itrivial
  iexact Hrest

/-- `lessor.Revoke.spec` at a plain spec over any connection (the form before auth-lease S4's §2.2). -/
abbrev lessor.Revoke.specP : Prop :=
  ∀ (l : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbLeaseRevokeRequest pbLeaseRevokeResponse)
    (Q : LeaseRevokeRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (lessorRemoteAt l addr ∗
      isGrpcRpcs addr go!"/etcdserverpb.Lease/LeaseRevoke" Spec ∗ □ ▷ Spec id Q ∗
      ctxOk ctx cd ∗ ctxErrClient ctx cd) }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Revoke"))
      (Val #(GoInterface.ok ctx))) (Val #id))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseRevokeRespM, leaseRevokeRespMsg resp m ∗ Q m) ∨
      (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗
        go_etcd_io.etcd.cache.v3.statusErrOk err)) }}

theorem lessor.Revoke.specP_of (h : lessor.Revoke.spec (GF := GF) (hG := hG)) :
    lessor.Revoke.specP (GF := GF) (hG := hG) := by
  intro l addr Spec Q ctx cd id
  iintro %Φ ⟨#Hpkg, Hlt, #Hrem, #Hrpc, #Hpre, #Hctx, Hrest⟩ HΦ
  ihave ⟨%conn, #HremC⟩ := (lessorRemoteAt_conn l addr).1 $$ Hrem
  ihave #HctxO := ctxOk_outgoingC ctx cd $$ Hctx
  iunfold metadata.outgoingCtxOkC at HctxO
  icases HctxO with ⟨%om, #Hom⟩
  iapply (h l conn addr (GrpcSpec.md Spec) Q ctx om cd id) $$ [Hlt Hrest] HΦ
  iframe Hlt Hpkg HremC Hom Hctx
  isplitr
  · iapply (isGrpcRpcs_md addr _ Spec).1 $$ Hrpc
  isplitr
  · iintro !>; inext
    unfold attemptPre
    iintro %md -
    simp only [GrpcSpec.md]
    isplitl
    · iexact Hpre
    · iintro !> %_; itrivial
  iexact Hrest

/-- `lessor.TimeToLive.spec` at a plain spec over any connection (the form before auth-lease S4's §2.2). -/
abbrev lessor.TimeToLive.specP : Prop :=
  ∀ (l : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbLeaseTimeToLiveRequest pbLeaseTimeToLiveResponse)
    (Q : LeaseTTLRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (id : w64) (sl : GoSlice) (gs : List (Bool → Bool)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (lessorRemoteAt l addr ∗
      isGrpcRpcs addr go!"/etcdserverpb.Lease/LeaseTimeToLive" Spec ∗
      □ ▷ Spec (id, leaseKeysFold gs false) Q ∗ leaseOptsAt sl gs ∗
      ctxOk ctx cd ∗ ctxErrClient ctx cd) }}
    (App (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!!
        go!"TimeToLive")) (Val #(GoInterface.ok ctx))) (Val #id)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : LeaseTTLRespM) (h : Loc) (ks : GoSlice),
        structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"ResponseHeader" resp ↦□ h ∗
        hdrFull h m.hdr ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"TTL" resp ↦□ m.ttl ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"GrantedTTL" resp ↦□
          m.grantedTtl ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"Keys" resp ↦□ ks ∗ Q m) ∨
      (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗
        go_etcd_io.etcd.cache.v3.statusErrOk err)) }}

theorem lessor.TimeToLive.specP_of (h : lessor.TimeToLive.spec (GF := GF) (hG := hG)) :
    lessor.TimeToLive.specP (GF := GF) (hG := hG) := by
  intro l addr Spec Q ctx cd id osl gs
  iintro %Φ ⟨#Hpkg, Hlt, #Hrem, #Hrpc, #Hpre, Hopt, #Hctx, Hrest⟩ HΦ
  ihave ⟨%conn, #HremC⟩ := (lessorRemoteAt_conn l addr).1 $$ Hrem
  ihave #HctxO := ctxOk_outgoingC ctx cd $$ Hctx
  iunfold metadata.outgoingCtxOkC at HctxO
  icases HctxO with ⟨%om, #Hom⟩
  iapply (h l conn addr (GrpcSpec.md Spec) Q ctx om cd id osl gs) $$ [Hlt Hopt Hrest] HΦ
  iframe Hlt Hpkg HremC Hom Hctx Hopt
  isplitr
  · iapply (isGrpcRpcs_md addr _ Spec).1 $$ Hrpc
  isplitr
  · iintro !>; inext
    unfold attemptPre
    iintro %md -
    simp only [GrpcSpec.md]
    isplitl
    · iexact Hpre
    · iintro !> %_; itrivial
  iexact Hrest

/-- `lessor.Leases.spec` at a plain spec over any connection (the form before auth-lease S4's §2.2). -/
abbrev lessor.Leases.specP : Prop :=
  ∀ (l : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbLeaseLeasesRequest pbLeaseLeasesResponse)
    (Q : LeaseLeasesRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (lessorRemoteAt l addr ∗
      isGrpcRpcs addr go!"/etcdserverpb.Lease/LeaseLeases" Spec ∗ □ ▷ Spec () Q ∗
      ctxOk ctx cd ∗ ctxErrClient ctx cd) }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Leases"))
      (Val #(GoInterface.ok ctx)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : LeaseLeasesRespM) (h : Loc) (sl : GoSlice),
        structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"ResponseHeader" resp ↦□ h ∗
        hdrFull h m.hdr ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
        sl ↦* (m.ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗ Q m) ∨
      (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗
        go_etcd_io.etcd.cache.v3.statusErrOk err)) }}

theorem lessor.Leases.specP_of (h : lessor.Leases.spec (GF := GF) (hG := hG)) :
    lessor.Leases.specP (GF := GF) (hG := hG) := by
  intro l addr Spec Q ctx cd 
  iintro %Φ ⟨#Hpkg, Hlt, #Hrem, #Hrpc, #Hpre, #Hctx, Hrest⟩ HΦ
  ihave ⟨%conn, #HremC⟩ := (lessorRemoteAt_conn l addr).1 $$ Hrem
  ihave #HctxO := ctxOk_outgoingC ctx cd $$ Hctx
  iunfold metadata.outgoingCtxOkC at HctxO
  icases HctxO with ⟨%om, #Hom⟩
  iapply (h l conn addr (GrpcSpec.md Spec) Q ctx om cd ) $$ [Hlt Hrest] HΦ
  iframe Hlt Hpkg HremC Hom Hctx
  isplitr
  · iapply (isGrpcRpcs_md addr _ Spec).1 $$ Hrpc
  isplitr
  · iintro !>; inext
    unfold attemptPre
    iintro %md -
    simp only [GrpcSpec.md]
    isplitl
    · iexact Hpre
    · iintro !> %_; itrivial
  iexact Hrest

end plain

end EtcdGrove
end Perennial
