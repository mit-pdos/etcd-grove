/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__LeaseTimeToLive.lean`. Lean-first
(no Rocq counterpart); the lease-read plan (2026-10-31).

`requireAuthInfo`, then (with `Keys`) `checkLeaseTimeToLive`, the contract `leaseTimeToLive`, and
(with `Keys`) the auth store's revision re-check, whose verdict the spec does not state (an
`ErrAuthOldRevision` is an `applyErrIs` error).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseTimeToLive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__leaseTimeToLive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkLeaseTimeToLive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__requireAuthInfo
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthStore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheckLemmas

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

theorem EtcdServer.LeaseTimeToLive.wp_proof
    (hReq : EtcdServer.requireAuthInfo.spec (GF := GF) (hG := hG))
    (hChk : EtcdServer.checkLeaseTimeToLive.spec (GF := GF) (hG := hG))
    (hTTL : EtcdServer.leaseTimeToLive.spec (GF := GF) (hG := hG))
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    EtcdServer.LeaseTimeToLive.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr γl ctx cd r dq v n m
  wp_start as ⟨#Hq, #Hr, #Hau, #Hlb, #Hlr, #Hpub, #Hmlb, #Hctx, HRD, #Hpool, Htok, %Hbound, Hreq⟩
  ihave ⟨%st, %cca, #Has, #Hreqa, #Hreqb, #Hcca, #HLb⟩ := leaseCheckSetup s E n $$ [$Hau $Hlb $Hpub]
  iunfold isAuthStoreLeaseLb at HLb
  icases HLb with ⟨%ai, %Hai, #HEn, #HRev, -, -, -⟩
  subst Hai
  ihave #Hap : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
  · iPkgInit
  ihave ⟨-, ⟨%eOR, #HOR, #HORe⟩⟩ := leaseCheckErrs $$ Hap
  ihave #Htx : mvcc.txnCtx (GF := GF) ctx cd $$ []
  · iunfold mvcc.txnCtx; iright; iexact Hctx
  (try wp_auto)
  wp_apply (hReq s E ctx cd) $$ [$HRD] as %err ⟨HRD, #Hout⟩
  · iframe #
  ihave #Hout' := Hout
  iunfold authedOutB at Hout'
  icases Hout' with ⟨#Herr, -⟩
  (try wp_auto)
  rcases err with ei | _
  · (try wp_auto)
    iapply HΦ
    iframe HRD Htok Hreq
    iright
    iframe Herr
    ipureintro; exact ⟨rfl, by intro h; cases h⟩
  (try wp_auto)
  ihave ⟨Hreq, %Hrn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hreq
  iStructNamed Hreq
  cases hK : v.Keys' with
  | true =>
    (try wp_auto)
    -- `rev, err = s.checkLeaseTimeToLive(ctx, lease.LeaseID(r.ID))`
    wp_apply (hChk s E γl ctx cd v.ID' n m) $$ [$HRD $Htok] as %rev0 %err1
        ⟨HRD, Htok, #He1, Hok⟩
    · iframe #; ipureintro; exact Hbound
    (try wp_auto)
    rcases err1 with ei | _
    · (try wp_auto)
      ihave Hreq : r ↦{dq} v $$ [state ID Keys unknownFields sizeCache]
      · iapply typedPointsto_combine _ _ _ Hrn
        simp only [TypedPointsto.typedPointstoDef, hK]
        iframe
      iapply HΦ
      iframe HRD Htok Hreq
      iright
      iframe He1
      ipureintro; exact ⟨rfl, by intro h; cases h⟩
    icases Hok $$ %rfl with ⟨#Hrv, #Hchk⟩
    (try wp_auto)
    ihave Hreq : r ↦{dq} v $$ [state ID Keys unknownFields sizeCache]
    · iapply typedPointsto_combine _ _ _ Hrn
      simp only [TypedPointsto.typedPointstoDef, hK]
      iframe
    -- `resp, err := s.leaseTimeToLive(ctx, r)`
    wp_apply (hTTL s E ρ γr γl ctx cd r dq v) $$ [$Htok $Hreq] as %resp %err2
        ⟨Htok, Hreq, Hres⟩
    · iframe #; ipureintro; exact Hbound
    icases Hres with (⟨%He2, %w, Hw, %Hh, %Hid, Hhv⟩ | ⟨%Hn, #He2⟩)
    · subst He2
      (try wp_auto)
      ihave ⟨Hreq, -⟩ := typedPointsto_not_null_dup _ _ _ $$ Hreq
      iStructNamed Hreq
      (try wp_auto)
      try rw [hK]
      (try wp_auto)
      -- `if s.AuthStore().IsAuthEnabled() && rev != s.AuthStore().Revision()`
      wp_apply (hAS s _) as -
      · iframe #
      (try wp_auto)
      wp_apply HEn $$ [$HRD] as %b ⟨HRD, -⟩
      ihave Hreq : r ↦{dq} v $$ [state ID Keys unknownFields sizeCache]
      · iapply typedPointsto_combine _ _ _ Hrn
        simp only [TypedPointsto.typedPointstoDef, hK]
        iframe
      (try wp_auto)
      cases b with
      | false =>
        (try wp_auto)
        iapply HΦ
        iframe HRD Htok Hreq
        ileft
        isplitr
        · ipureintro; rfl
        iframe Hout
        isplitl [Hw Hhv]
        · iexists w; iframe Hw Hhv; ipureintro; exact ⟨Hh, Hid⟩
        (try simp only [↓reduceIte]); iexact Hchk
      | true =>
        (try wp_auto)
        wp_apply (hAS s _) as -
        · iframe #
        (try wp_auto)
        wp_apply HRev as %rev2 -
        (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          iapply HΦ
          iframe HRD Htok Hreq
          ileft
          isplitr
          · ipureintro; rfl
          iframe Hout
          isplitl [Hw Hhv]
          · iexists w; iframe Hw Hhv; ipureintro; exact ⟨Hh, Hid⟩
          (try simp only [↓reduceIte]); iexact Hchk
        · -- `return nil, auth.ErrAuthOldRevision`
          (try wp_auto)
          iapply HΦ
          iframe HRD Htok Hreq
          iright
          iframe HORe
          ipureintro; exact ⟨rfl, by intro h; cases h⟩
    · obtain ⟨rfl, Hne⟩ := Hn
      rcases err2 with ei | _
      · (try wp_auto)
        iapply HΦ
        iframe HRD Htok Hreq
        iright
        iframe He2
        ipureintro; exact ⟨rfl, Hne⟩
      · exact absurd rfl Hne
  | false =>
    (try wp_auto)
    ihave Hreq : r ↦{dq} v $$ [state ID Keys unknownFields sizeCache]
    · iapply typedPointsto_combine _ _ _ Hrn
      simp only [TypedPointsto.typedPointstoDef, hK]
      iframe
    wp_apply (hTTL s E ρ γr γl ctx cd r dq v) $$ [$Htok $Hreq] as %resp %err2
        ⟨Htok, Hreq, Hres⟩
    · iframe #; ipureintro; exact Hbound
    icases Hres with (⟨%He2, %w, Hw, %Hh, %Hid, Hhv⟩ | ⟨%Hn, #He2⟩)
    · subst He2
      (try wp_auto)
      ihave ⟨Hreq, -⟩ := typedPointsto_not_null_dup _ _ _ $$ Hreq
      iStructNamed Hreq
      (try wp_auto)
      try rw [hK]
      (try wp_auto)
      ihave Hreq : r ↦{dq} v $$ [state ID Keys unknownFields sizeCache]
      · iapply typedPointsto_combine _ _ _ Hrn
        simp only [TypedPointsto.typedPointstoDef, hK]
        iframe
      iapply HΦ
      iframe HRD Htok Hreq
      ileft
      isplitr
      · ipureintro; rfl
      iframe Hout
      isplitl [Hw Hhv]
      · iexists w; iframe Hw Hhv; ipureintro; exact ⟨Hh, Hid⟩
      (try simp only [↓reduceIte, Bool.false_eq_true]); itrivial
    · obtain ⟨rfl, Hne⟩ := Hn
      rcases err2 with ei | _
      · (try wp_auto)
        iapply HΦ
        iframe HRD Htok Hreq
        iright
        iframe He2
        ipureintro; exact ⟨rfl, Hne⟩
      · exact absurd rfl Hne

end proof

end EtcdGrove
end Perennial
