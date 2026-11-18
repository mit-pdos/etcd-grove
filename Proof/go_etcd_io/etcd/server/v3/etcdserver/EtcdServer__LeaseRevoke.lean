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
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.StartLaws

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
  intro s E ρ ctx cd tok r id Q
  have hRR := hRR0 s E ρ
  wp_start as ⟨%hlm, #Hsrv, #Hau, Hlt, Hrd, #Hcred, #Hctx, #Hlib, #HtokC, #Hspc, #Hst, #Hreq, Hperm⟩
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
  wp_apply (traceutil.Tracer.Start.spec_txn hTS) tr ctx cd _ _ $$ [] as %ctx1 %sp ⟨⟨%vs1, #Hctx1t, Hctx1w⟩, #Hctr1, #Hmd1, #Hsp, #Hspw, #Hst1, #Hlibw, -⟩
  · iframe #; iunfold mvcc.txnCtx; iright; iexact Hctx
  ihave #Hstc1 := Hst1 $$ Hst
  ihave #Hctx1 := Hctx1w $$ Hctx
  ihave #Hlib1 := Hlibw $$ Hlib
  ihave #Hspc1 := Hspw $$ Hspc
  -- (sweep repairs 1, B2) the request context's start time, kept by `Start`
  ihave #Hstc1 := Hst1 $$ Hst
  iunfold trace.isSpan at Hsp
  icases Hsp with ⟨%si, %Hsi, #HEnd, -, -⟩
  subst Hsi
  (try wp_auto)
  -- `requireAuthInfo`: `nil` with auth off; with auth on, its error is returned
  ihave #HtokE := auth.ctxToken_transfer_gate E.authOn ctx ctx1 tok $$ [$Hmd1 $HtokC]
  ihave #HtokA : □ (⌜E.authMode.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx1) tok) $$ []
  · iintro !> %h; iapply HtokE; ipureintro; exact h
  wp_apply hAuth s E ctx1 _ tok $$ [Hrd] as %aerr ⟨Hrd, #Hae, -⟩
  · iframe #; iframe Hrd
  (try wp_auto)
  rcases aerr with ae | _
  · -- refused
    (try wp_auto)
    wp_apply HEnd
    (try wp_auto)
    iapply HΦ
    iframe Hlt Hrd
    iright
    iunfold authedOutB at Hae
    icases Hae with ⟨#HaE, -⟩
    iframe HaE
    ipureintro; exact ⟨rfl, by intro h; cases h⟩
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
  let rq : apply.IRRModel := irrLeaseRevoke id
  have Hk : apply.dispatchKind rq = .leaseRevoke := by
    simp [rq, irrLeaseRevoke, apply.dispatchKind, apply.irrEmpty]
  have Hrk : apply.revokeKindOk rq :=
    ⟨Hk, by simp [rq, irrLeaseRevoke, apply.needAdminPermission, apply.irrEmpty],
      by simp [rq, irrLeaseRevoke, apply.noSideEffect, apply.irrEmpty]⟩
  have HnzW : irrNoZeroEnd rq := by
    refine ⟨?_, ?_, ?_⟩ <;> intro _ h <;> simp [rq, irrLeaseRevoke, apply.irrEmpty] at h
  have Hshape : rqShape ρ.kv.lm rq := by
    refine ⟨fun on => ⟨by rw [Hk]; decide, by rw [Hk]; intro h; cases h⟩, fun log hs => ?_⟩
    have hput : apply.putOk log ∧ (mvcc.stateAfter log).length ≤ 2 ^ 62 := by
      unfold rqSmall at hs; rw [Hk] at hs; exact hs
    exact (apply.rqOk_leaseRevoke _ _ _ Hk).2 ⟨hlm, Hrk, hput.1, hput.2⟩
  ihave #HirrNo : irrNoHdrIs «$a1_ptr» rq $$ []
  · iunfold irrNoHdrIs
    simp only [rq, irrLeaseRevoke, apply.irrEmpty, apply.optReqIs, apply.presentIs, apply.irrField, apply.leaseRevokeIs]
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
  cases hon : E.authOn
  · -- auth off
    rw [hon] at hRR
    ihave #HtokR : □ (⌜false = true⌝ → auth.ctxToken (GoInterface.ok ctx1) tok) $$ []
    · iintro !> %h; cases h
    imod Hcred with Hc
    wp_apply hRR ctx1 _ tok «$a1_ptr» rq (fun _ _ => iprop(True)) [] rfl
        (apply.irrDepthOk_of_txnW_none rfl)
        $$ [Hlt Hrd Hc Header] as %resp %err ⟨Hlt, Hrd, Hres⟩
    · iframe # Hlt Hrd Hc
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
      isplitl [Hown]
      · iunfold leaseRevokedResp
        iexists hh, rv
        iframe Hh Hrv Hown
        isplitr
        · ipureintro; intro h; subst h; simp at Hrvl; omega
        iunfold srvRevLb
        iexists log
        iframe Hic Hcok
        ipureintro; omega
      isplitr
      · iexact Hae
      iunfold leaseRevokeResM; itrivial
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
  · -- auth on (auth-lease S3b)
    rw [hon] at hRR
    ihave #HtokR : □ (⌜true = true⌝ → auth.ctxToken (GoInterface.ok ctx1) tok) $$ []
    · iintro !> -; iapply HtokA; ipureintro; first | rfl | exact hon
    -- (auth-lease S3b) the client's update, fired at the commit when granted
    imod kvResTok_alloc (GF := GF) with ⟨%γc, Htok⟩
    imod Hcred with Hc
    wp_apply hRR ctx1 _ tok «$a1_ptr» rq (revokeQhOn ρ.kv id γc Q) [] rfl
        (apply.irrDepthOk_of_txnW_none rfl)
        $$ [Hlt Hrd Hc Header Hperm] as %resp %err ⟨Hlt, Hrd, Hres⟩
    · iframe # Hlt Hrd Hc
      isplitl [Hperm]
      · iapply leaseRevokePermit_reqPropOk ρ.raft ρ.kv _ _ id Q γc
          (fun _ => BIBase.Entails.rfl) ⟨hlm, Hrk⟩ $$ Hperm
      iexists _; iexact Header
    (try wp_auto)
    icases Hres with (⟨%Herr, %hm, %rq', %Lq, %Hwire, -, Hok, #HpAf, #HQq, #Hhb⟩ | ⟨%Hre, #HaE, -⟩)
    · subst Herr
      have Hrq : rq' = apply.withHeader rq hm := Hwire.2.2.2 HnzW
      subst Hrq
      iunfold appliedOkM at Hok
      icases Hok with ⟨%x, %x', %o, %skip, %Hstep0, Hda, -, -, -, -, -, -, -, -, Hans⟩
      have Hk' : apply.dispatchKind (apply.withHeader rq hm) = .leaseRevoke := by
        rw [← Hk]; exact Hwire.2.2.1.trans rfl
      obtain ⟨-, -, -, Hmo, -⟩ := Hstep0
      -- (auth-lease S3b) a success is not the auth layer's refusal (whose answer is its error), so
      -- the revocation was granted (`authTie`)
      iunfold apply.dispatchAnswer at Hda
      rw [Hk']
      icases Hda with ⟨%r'', -, Hro⟩
      ihave %Hne : ⌜o ≠ .rejected .auth⌝ $$ [Hro]
      · cases o with
        | applied _ _ => ipureintro; intro h; cases h
        | rejected k =>
          cases k
          case auth =>
            iunfold apply.revokeOutcomeIs at Hro
            simp only [apply.rejErrIs]
            icases Hro with ⟨-, %Hn, -⟩
            exact absurd rfl Hn
          all_goals (ipureintro; intro h; cases h)
      have Hga := grantedAt_of_dispatched ρ.kv _ Lq x.log o skip (by rw [Hk']; rfl) Hne Hmo
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
      wp_auto_lc 1
      -- the client's result
      iunfold revokeQhOn at HQq
      iunfold grantedRes at HQq
      icases HQq with (⟨-, #HQr⟩ | %Hng)
      rotate_left
      · exact absurd Hga Hng
      imod kvRes_take γc Q _ ⊤ CoPset.subseteq_top $$ HQr Htok Hlc1 with HQ
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
      isplitl [Hown]
      · iunfold leaseRevokedResp
        iexists hh, rv
        iframe Hh Hrv Hown
        isplitr
        · ipureintro; intro h; subst h; simp at Hrvl; omega
        iunfold srvRevLb
        iexists log
        iframe Hic Hcok
        ipureintro; omega
      isplitr
      · iexact Hae
      iunfold leaseRevokeResM
      iexists hm, Lq
      iframe HpAf HQ
      isplitr
      · iexact Hhb
      ipureintro; exact Hga
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
