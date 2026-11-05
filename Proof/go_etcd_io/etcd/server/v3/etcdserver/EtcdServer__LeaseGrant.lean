/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__LeaseGrant.lean`. Lean-first (no
Rocq counterpart); the lease-grant plan's 2.5 (2026-11-03). Its callees: the id generator's `Next`,
the span's (`Tracer.Start`, `WithAttributes`, `Int64`, the request's `GetTTL`), `requireAuthInfo`
(`nil` with auth off) and `raftRequest` (the grant proposed through `reqPropOk`'s grant disjunct, its
answer `grantAnsM`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseGrant
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__requireAuthInfo
public import Spec.go_etcd_io.etcd.pkg.v3.idutil.Generator__Next
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.LeaseGrantRequest__GetTTL
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
theorem EtcdServer.LeaseGrant.wp_proof
    (hNext : idutil.Generator.Next.spec (GF := GF) (hG := hG))
    (hAuth : EtcdServer.requireAuthInfo.spec (GF := GF) (hG := hG))
    (hRR0 : EtcdServer.raftRequest.spec (GF := GF) (hG := hG))
    (hTTL : LeaseGrantRequest.GetTTL.spec (GF := GF) (hG := hG))
    (hTS : traceutil.Tracer.Start.spec (GF := GF) (hG := hG))
    (hWA : trace.WithAttributes.spec (GF := GF) (hG := hG))
    (hI64 : «attribute».Int64.spec (GF := GF) (hG := hG)) :
    EtcdServer.LeaseGrant.spec (GF := GF) (hG := hG) := by
  intro s E ρ ctx cd r ttl id0 hg hrev
  obtain ⟨hlg, hoff⟩ := hg
  have hRR := hRR0 s E ρ
  rw [hoff] at hRR
  wp_start as ⟨#Hsrv, #Hau, Hlt, Hrd, #Hcred, #Hctx, Hreq⟩
  iunfold leaseGrantReqOwn at Hreq
  icases Hreq with ⟨%hr, #HTTL, HID⟩
  ihave #Hsrv' := Hsrv
  iunfold isServerReq at Hsrv'
  icases Hsrv' with ⟨⟨%v, #Hf⟩, -⟩
  iunfold srvReqFieldsAt at Hf
  icases Hf with ⟨#Hgen, #HidG, -⟩
  ihave #Pid : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨-, -, -, ⟨%tr, #Htr⟩, -⟩, -⟩
  (try wp_auto)
  -- the loop: a fresh id while `r.ID` is `0`
  -- (the lease-expiry plan's E3 (b)) in the revocable mode, the generated id's claim right kept
  ihave HI : (∃ i : w64, structFieldRef etcdserverpb.LeaseGrantRequest go!"ID" r ↦ i ∗
      (⌜i = W64 0 ∨ ρ.kv.lm ≠ .revocable⌝ ∨
        ∃ u : w64, ⌜i = u &&& leaseIdMask ∧ idPfx u = ρ.ids.pfx⌝ ∗ idUnclaimed ρ.ids u)) $$ [HID]
  · iexists _; iframe HID; ileft; ipureintro
    by_cases hm : ρ.kv.lm = .revocable
    · exact Or.inl (hrev hm)
    · exact Or.inr hm
  wp_for HI
  icases HI with ⟨HI, Hu⟩
  (try wp_auto)
  wp_if_destruct
  · iclear Hu
    imod Hcred with Hc
    wp_apply hNext ρ.ids v.gen (srvFloorFact E) $$ [Hc] as %nid ⟨Hfr, -⟩
    · iframe #; iframe Hc
    (try wp_auto)
    wp_for_post
    iframe
    iexists _; iframe
    iright
    iunfold idFresh at Hfr
    icases Hfr with ⟨Hun, -, %Hpf⟩
    iexists nid; iframe Hun
    ipureintro; exact ⟨rfl, Hpf⟩
  have hid : i ≠ W64 0 := fun h => Hif (by subst h; rfl)
  rw [decide_eq_false hid]; simp only [Bool.false_eq_true, ↓reduceIte]
  ipersist HI
  (try wp_auto)
  wp_apply hI64 as %kv1 -
  (try wp_auto)
  wp_apply hTTL r ttl _ $$ [] as -
  · iframe #
  (try wp_auto)
  wp_apply hI64 as %kv2 -
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
  wp_apply hTS tr ctx cd _ _ $$ [] as %ctx1 %sp ⟨⟨%vs1, #Hctx1t, Hctx1w⟩, #Hctr1, %Hinc1, #Hsp⟩
  · iframe #; iunfold mvcc.txnCtx; iright; iexact Hctx
  ihave #Hctx1 := Hctx1w $$ Hctx
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
  -- `&pb.InternalRaftRequest{LeaseGrant: r}`
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
  let rq : apply.IRRModel := { apply.irrEmpty with leaseGrant := some ⟨i, ttl⟩ }
  have Hk : apply.dispatchKind rq = .leaseGrant := by
    simp [rq, apply.dispatchKind, apply.irrEmpty]
  have Hgk : apply.grantKindOk rq := by
    refine ⟨Hk, by simp [rq, apply.needAdminPermission, apply.irrEmpty],
      by simp [rq, apply.noSideEffect, apply.irrEmpty], ?_⟩
    intro g hg'
    simp only [rq, Option.some.injEq] at hg'
    subst hg'; exact hid
  have HnzW : irrNoZeroEnd rq := by
    refine ⟨?_, ?_, ?_⟩ <;> intro _ h <;> simp [rq, apply.irrEmpty] at h
  have Hshape : rqShape ρ.kv.lm rq := by
    refine ⟨fun on => ⟨by rw [Hk]; decide, by rw [Hk]; intro h; cases h⟩, fun log _ => ?_⟩
    exact (apply.rqOk_leaseGrant _ _ _ Hk).2 ⟨KVNames.lm_of_lg_true hlg, Hgk⟩
  ihave #HirrNo : irrNoHdrIs «$a1_ptr» rq $$ []
  · iunfold irrNoHdrIs
    simp only [rq, apply.irrEmpty, apply.optReqIs, apply.presentIs, apply.irrField, apply.leaseGrantIs]
    isplitr
    · ipureintro; exact Hirrn
    isplitr
    · have h0 : (W64 0 : w64) = 0 := by decide
      rw [h0]; iexact ID
    repeat (isplitr; · iexists _; iframe #; try (ipureintro; first | exact hr | simp))
    iexists _; iframe #; try (ipureintro; first | exact hr | simp)
  imod mvcc.idxCert_nil E.γ.idx with #HF
  imod Hcred with Hc
  wp_apply hRR ctx1 _ «$a1_ptr» rq (fun _ _ => iprop(True)) [] rfl
      (apply.irrDepthOk_of_txnW_none rfl)
      $$ [Hlt Hrd Hc Header Hu] as %resp %err ⟨Hlt, Hrd, Hres⟩
  · iframe # Hlt Hrd Hc
    isplitr
    · rw [isServerReqM_false]; iexact Hsrv
    isplitl [Hu]
    · iunfold reqPropOkM
      try dsimp only
      isplitl
      rotate_left
      · ipureintro; exact attrIdOk_of_kind _ rq (by rw [Hgk.1]; intro hk; cases hk)
      iexists (fun _ => iprop(True))
      isplitl
      · iunfold reqPropOk
        iright; iright
        isplitr
        · ipureintro; exact ⟨Or.inl ⟨KVNames.lm_of_lg_true hlg, Hgk⟩, Hshape, HnzW, rfl⟩
        -- (the lease-expiry plan's E3 (b)) in the revocable mode, the generated id's claim right
        by_cases hm : ρ.kv.lm = .revocable
        · have hr : rqRevGrantId ρ.kv.lm rq = some i := by
            unfold rqRevGrantId; rw [if_pos ⟨hm, Hk⟩]; rfl
          iunfold grantIdOwn
          rw [hr]
          icases Hu with (%Hu | Hu)
          · exfalso; rcases Hu with h | h
            · exact hid h
            · exact h hm
          iexact Hu
        · iapply grantIdOwn_nonRev ρ.kv rq hm
      ipureintro; rfl
    iexists _; iexact Header
  (try wp_auto)
  icases Hres with (⟨%Herr, %hm, %rq', %Lq, %Hwire, -, Hok, -, -, -⟩ | ⟨%Hre, #HaE, -⟩)
  · subst Herr
    have Hrq : rq' = apply.withHeader rq hm := Hwire.2.2.2 HnzW
    subst Hrq
    iunfold appliedOkM at Hok
    icases Hok with ⟨%x, %x', %o, %skip, -, -, -, -, -, -, -, Hans, -⟩
    have Hk' : apply.dispatchKind (apply.withHeader rq hm) = .leaseGrant := by
      rw [← Hk]; exact Hwire.2.2.1.trans rfl
    iunfold grantAnsM at Hans
    rw [if_pos Hk']
    have hlg' : (apply.withHeader rq hm).leaseGrant = some ⟨i, ttl⟩ := rfl
    iunfold apply.grantAnswer at Hans
    rw [hlg']
    icases Hans with ⟨%r', %Hresp, Hans⟩
    icases Hans with (⟨-, Hri, %gi, #Hgr⟩ | %Hne)
    rotate_left
    · exact absurd rfl Hne
    subst Hresp
    iunfold apply.grantRespIs at Hri
    icases Hri with ⟨%Hrn, #Hid', ⟨%t, #Ht⟩, ⟨%e, #He⟩, %log, Hhdr⟩
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
    iunfold leaseGrantedResp
    icases Hgr with ⟨%gl, %gt, #Hgl, #Hgt, %Hgtge⟩
    iexists i, t, e, gi, hh, rv
    iframe Hh Hrv Hown Hid' Ht He
    isplitr
    · ipureintro; intro h; subst h; simp at Hrvl; omega
    isplitr
    · iunfold srvRevLb
      iexists log
      iframe Hic Hcok
      ipureintro; omega
    isplitr
    · ipureintro; exact hid
    iexists gl, gt
    iframe Hgl Hgt
    ipureintro; exact Hgtge
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
