/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__LeaseRevoke.lean`. Lean-first (no
Rocq counterpart); the lease-expiry plan's X6 (2026-11-04), `EtcdServer.LeaseGrant`'s proof mirrored.
Its callees: the span's (`Tracer.Start`, `WithAttributes`, `Int64`, the request's `GetID`),
`requireAuthInfo` (`nil` with auth off) and `raftRequest` (the revocation proposed through
`reqPropOk`'s revocation form, its answer `revokeAnsM`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__requireAuthInfo
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.LeaseRevokeRequest__GetID
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Tracer__Start
public import Spec.go_opentelemetry_io.otel.trace.WithAttributes
public import Spec.go_opentelemetry_io.otel.attribute.Int64
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposerLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem EtcdServer.LeaseRevoke.wp_proof
    (hAuth : EtcdServer.requireAuthInfo.spec (GF := GF) (hG := hG))
    (hRR0 : EtcdServer.raftRequest.spec (GF := GF) (hG := hG))
    (hID : LeaseRevokeRequest.GetID.spec (GF := GF) (hG := hG))
    (hTS : traceutil.Tracer.Start.spec (GF := GF) (hG := hG))
    (hWA : trace.WithAttributes.spec (GF := GF) (hG := hG))
    (hI64 : «attribute».Int64.spec (GF := GF) (hG := hG)) :
    EtcdServer.LeaseRevoke.spec (GF := GF) (hG := hG) := by
  intro s E ρ ctx cd r id hv
  obtain ⟨hlm, hoff⟩ := hv
  have hRR := hRR0 s E ρ
  rw [hoff] at hRR
  wp_start as ⟨#Hsrv, #Hau, Hlt, Hrd, #Hcred, #Hctx, #Hspc, #Hst, #Hreq⟩
  iunfold leaseRevokeReqRO at Hreq
  icases Hreq with ⟨%hr, #HID⟩
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨-, -, -, ⟨%tr, #Htr⟩, -⟩, -⟩
  (try wp_auto)
  wp_apply hID r id _ $$ [] as -
  · iframe #
  (try wp_auto)
  wp_apply hI64 as %kv1 -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨-, -⟩
  (try wp_auto)
  wp_apply hWA as %opt -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨-, -⟩
  (try wp_auto)
  wp_apply hTS tr ctx cd _ _ $$ [] as %ctx1 %sp ⟨⟨%vs1, #Hctx1t, Hctx1w⟩, #Hctr1, %Hinc1, #Hsp, #Hspw, #Hst1⟩
  · iframe #; iunfold mvcc.txnCtx; iright; iexact Hctx
  ihave #Hstc1 := Hst1 $$ Hst
  ihave #Hctx1 := Hctx1w $$ Hctx
  ihave #Hspc1 := Hspw $$ Hspc
  -- (sweep repairs 1, B2) the request context's start time, kept by `Start`
  ihave #Hstc1 := Hst1 $$ Hst
  iunfold trace.isSpan at Hsp
  icases Hsp with ⟨%si, %Hsi, #HEnd, -, -⟩
  subst Hsi
  (try wp_auto)
  -- `requireAuthInfo`: `nil` with auth off
  wp_apply hAuth s E ctx1 _ $$ [Hrd] as %aerr ⟨Hrd, #Hae, -⟩
  · iframe #; iframe Hrd
  iunfold authedOutB at Hae
  icases Hae with ⟨-, %Hoffe, -⟩
  have hae : aerr = GoInterface.nil := Hoffe (by rw [← apply.AEnv.authOn_eq]; exact hoff)
  subst hae
  (try wp_auto)
  -- `&pb.InternalRaftRequest{LeaseRevoke: r}`
  ihave ⟨Hirr, %Hirrn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$a1»
  iStructNamed Hirr
  ipersist ID
  ipersist Range
  ipersist Put
  ipersist DeleteRange
  ipersist Txn
  ipersist Compaction
  ipersist LeaseGrant
  ipersist LeaseRevoke
  ipersist Alarm
  ipersist LeaseCheckpoint
  ipersist AuthEnable
  ipersist AuthDisable
  ipersist AuthStatus
  ipersist Authenticate
  ipersist AuthUserAdd
  ipersist AuthUserDelete
  ipersist AuthUserGet
  ipersist AuthUserChangePassword
  ipersist AuthUserGrantRole
  ipersist AuthUserRevokeRole
  ipersist AuthUserList
  ipersist AuthRoleList
  ipersist AuthRoleAdd
  ipersist AuthRoleDelete
  ipersist AuthRoleGet
  ipersist AuthRoleGrantPermission
  ipersist AuthRoleRevokePermission
  ipersist ClusterVersionSet
  ipersist ClusterMemberAttrSet
  ipersist DowngradeInfoSet
  ipersist DowngradeVersionTest
  let rq : apply.IRRModel := { apply.irrEmpty with leaseRevoke := some id }
  have Hk : apply.dispatchKind rq = .leaseRevoke := by
    simp [rq, apply.dispatchKind, apply.irrEmpty]
  have Hrk : apply.revokeKindOk rq :=
    ⟨Hk, by simp [rq, apply.needAdminPermission, apply.irrEmpty],
      by simp [rq, apply.noSideEffect, apply.irrEmpty]⟩
  have HnzW : irrNoZeroEnd rq := by
    refine ⟨?_, ?_, ?_⟩ <;> intro _ h <;> simp [rq, apply.irrEmpty] at h
  have Hshape : rqShape ρ.kv.lm rq := by
    refine ⟨fun on => ⟨by rw [Hk]; decide, by rw [Hk]; intro h; cases h⟩, fun log hs => ?_⟩
    have hput : apply.putOk log ∧ (mvcc.stateAfter log).length ≤ 2 ^ 62 := by
      unfold rqSmall at hs; rw [Hk] at hs; exact hs
    exact (apply.rqOk_leaseRevoke _ _ _ Hk).2 ⟨hlm, Hrk, hput.1, hput.2⟩
  ihave #HirrNo : irrNoHdrIs «$a1_ptr» rq $$ []
  · iunfold irrNoHdrIs
    simp only [rq, apply.irrEmpty, apply.optReqIs, apply.presentIs, apply.irrField, apply.leaseRevokeIs]
    isplitr
    · ipureintro; exact Hirrn
    isplitr
    · have h0 : (W64 0 : w64) = 0 := by decide
      rw [h0]; iexact ID
    repeat (isplitr; · iexists _; iframe #; try (ipureintro; first | exact hr | simp))
    iexists _; iframe #; try (ipureintro; first | exact hr | simp)
  imod monoListLbOwn_nil (GF := GF) E.γs.slog with #HF0
  ihave #HF : srvApi.kvLogLb E.γs [] $$ []
  · iunfold srvApi.kvLogLb; iexact HF0
  imod Hcred with Hc
  wp_apply hRR ctx1 _ «$a1_ptr» rq (fun _ _ => iprop(True)) [] rfl
      (apply.irrDepthOk_of_txnW_none rfl)
      $$ [Hlt Hrd Hc Header] as %resp %err ⟨Hlt, Hrd, Hres⟩
  · iframe # Hlt Hrd Hc
    isplitr
    · rw [isServerReqM_false]; iexact Hsrv
    isplitr
    · iunfold reqPropOkM
      try dsimp only
      isplitl
      rotate_left
      · ipureintro; exact attrIdOk_of_kind _ rq (by rw [Hk]; intro hk; cases hk)
      iexists (fun _ => iprop(True))
      isplitl
      · iunfold reqPropOk
        iright; iright
        isplitr
        · ipureintro; exact ⟨Or.inr ⟨hlm, Hrk⟩, Hshape, HnzW, rfl⟩
        iapply grantIdOwn_nonGrant ρ.kv rq (by rw [Hk]; intro hk; cases hk)
      ipureintro; rfl
    iexists _; iexact Header
  (try wp_auto)
  icases Hres with (⟨%Herr, %hm, %rq', %Lq, %Hwire, -, Hok, -, -, -⟩ | ⟨%Hre, #HaE, -⟩)
  · subst Herr
    have Hrq : rq' = apply.withHeader rq hm := Hwire.2.2.2 HnzW
    subst Hrq
    iunfold appliedOkM at Hok
    icases Hok with ⟨%x, %x', %o, %skip, -, -, -, -, -, -, -, -, -, -, Hans⟩
    have Hk' : apply.dispatchKind (apply.withHeader rq hm) = .leaseRevoke := by
      rw [← Hk]; exact Hwire.2.2.1.trans rfl
    iunfold revokeAnsM at Hans
    rw [if_pos Hk']
    have hlr' : (apply.withHeader rq hm).leaseRevoke = some id := rfl
    iunfold apply.revokeAnswer at Hans
    rw [hlr']
    icases Hans with ⟨%r', %Hresp, Hans⟩
    icases Hans with (⟨-, Hri⟩ | %Hne)
    rotate_left
    · exact absurd rfl Hne
    subst Hresp
    iunfold apply.revokeRespIs at Hri
    icases Hri with ⟨%Hrn, %log, Hhdr⟩
    iunfold apply.grantHdr at Hhdr
    icases Hhdr with ⟨Hown, %hh, %rv, #Hh, #Hrv, #Hic, #Hcok, %Hrvl⟩
    (try wp_auto)
    wp_apply HEnd
    (try wp_auto)
    iapply HΦ
    iframe Hlt Hrd
    ileft
    isplitr
    · ipureintro
      refine ⟨rfl, ?_⟩
      exact Hrn
    iunfold leaseRevokedResp
    iexists hh, rv
    iframe Hh Hrv Hown
    isplitr
    · ipureintro; intro h; subst h; simp at Hrvl; omega
    iunfold srvRevLb
    iexists log
    iframe Hic Hcok
    ipureintro; omega
  · obtain ⟨rfl, Hne⟩ := Hre
    (try wp_auto)
    rcases err with ei | _
    · (try wp_auto)
      wp_apply HEnd
      (try wp_auto)
      iapply HΦ
      iframe Hlt Hrd
      iright
      iframe HaE
      ipureintro; exact ⟨rfl, Hne⟩
    · exact absurd rfl Hne

end proof

end EtcdGrove
end Perennial
