/-
Proof of `Spec/.../authlease/noAuth.lean` (auth-lease S4, item 9, check 1). Lean-first (no Rocq
counterpart). Every call's success reply carries, at the token of one of its attempts (`akTokSeen`, from
the connection's token fact and `reqCtx`'s metadata), a passed lease check relative to `n`, which the
caller's premise refutes: the attempts' replies are `False`, so each call errs and `refused` returns.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.noAuth
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.reqCtx
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.refused
public import Spec.go_etcd_io.etcd.client.v3.lessor__Grant
public import Spec.go_etcd_io.etcd.client.v3.lessor__Revoke
public import Spec.go_etcd_io.etcd.client.v3.lessor__TimeToLive
public import Spec.go_etcd_io.etcd.client.v3.lessor__Leases
public import Spec.go_etcd_io.etcd.client.v3.WithAttachedKeys
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.LeaseAttempts
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.barrier
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client etcd_auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

theorem noAuth.wp_proof
    (wp_reqCtx : reqCtx.spec (GF := GF) (hG := hG))
    (wp_refused : refused.spec (GF := GF) (hG := hG))
    (wp_Grant : lessor.Grant.spec (GF := GF) (hG := hG))
    (wp_Revoke : lessor.Revoke.spec (GF := GF) (hG := hG))
    (wp_TimeToLive : lessor.TimeToLive.spec (GF := GF) (hG := hG))
    (wp_Leases : lessor.Leases.spec (GF := GF) (hG := hG))
    (wp_WithAttachedKeys : WithAttachedKeys.spec (GF := GF) (hG := hG)) :
    noAuth.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS cli who addr id s E ρ γa n ml Qg Qr hwho hAs
  wp_start as ⟨Hlt, #Htk, #Hsv, #Hn, #Hml, #Hno, #HQg, #HQr⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Htk0 := Htk
  iunfold clientTokAt at Htk0
  icases Htk0 with ⟨%api, %conn, -, -, #Htok, -, -, %lp, #Hlf, #Hrem⟩
  iunfold etcdstart.etcdLeaseServedOn at Hsv
  icases Hsv with ⟨#HrG, #HrR, #HrT, #HrL⟩
  (try wp_auto)
  -- `Grant`
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  have hout : akOut who = akOut who := rfl
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
  (try wp_auto)
  wp_apply (wp_Grant lp conn [addr] (etcdLeaseGrantSpecOn (srvTLSId s) E ρ (mvcc.api.mvccLeases E.γ)) (fun _ => iprop(|={⊤}=> False))
      ci (akOut who) cd grantTTLv) $$ [$Hlt] as %r %err ⟨Hlt, Hr⟩
  · iframe #
    iapply (grant_attempt_refuted s E ρ (mvcc.api.mvccLeases E.γ) γa who conn _ n grantTTLv Qg _ hout)
    iframe #
    isplitr
    · iintro !> %tok %K %m Hs Hck; iapply Hno $$ Hs Hck
    iintro !> %id'
    iapply HQg
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, %m, %h, -, -, -, -, Hf⟩ | ⟨%Herr, -⟩)
  · imod Hf with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  -- `Revoke(id)`
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  have hout : akOut who = akOut who := rfl
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
  (try wp_auto)
  wp_apply (wp_Revoke lp conn [addr] (etcdLeaseRevokeSpecOn (srvTLSId s) E ρ) (fun _ => iprop(|={⊤}=> False))
      ci (akOut who) cd id) $$ [$Hlt] as %r %err ⟨Hlt, Hr⟩
  · iframe #
    iapply (revoke_attempt_refuted s E ρ γa who conn _ n id Qr _ hout)
    iframe #
    isplitr
    · iintro !> %tok %K %m Hs Hck; iapply Hno $$ Hs Hck
    iintro !>
    iapply HQr
    · iexact Htok
    · ipureintro; exact hout
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, %m, -, Hf⟩ | ⟨%Herr, -⟩)
  · imod Hf with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  -- `TimeToLive(id)`
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  have hout : akOut who = akOut who := rfl
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
  (try wp_auto)
  ihave #Hnil := leaseOptsAt_nil (GF := GF)
  wp_apply (wp_TimeToLive lp conn [addr] (etcdLeaseTTLSpecMd (srvTLSId s) (leaseTTLRow s (mvcc.api.mvccLeases E.γ)) E (mvcc.api.mvccLeases E.γ)) (fun _ => iprop(|={⊤}=> False))
      ci (akOut who) cd id slice.nil []) $$ [$Hlt] as %r %err ⟨Hlt, Hr⟩
  · iframe #
    iapply (ttl_attempt_refuted s E (mvcc.api.mvccLeases E.γ) γa who conn _ n ml _ _ hout)
    iframe #
    iintro !> %tok %K %m Hs Hck; iapply Hno $$ Hs Hck
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, %m, %h, %ks, -, -, -, -, -, -, Hf⟩ | ⟨%Herr, -⟩)
  · imod Hf with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  -- `TimeToLive(id, WithAttachedKeys())`
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  have hout : akOut who = akOut who := rfl
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
  (try wp_auto)
  wp_apply wp_WithAttachedKeys as %f #Hf
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  ihave #Hopts := leaseOptsAt_one (GF := GF) _ f (fun _ => true) $$ [Hslo Hf]
  · iframe #
  (try wp_auto)
  wp_apply (wp_TimeToLive lp conn [addr] (etcdLeaseTTLSpecMd (srvTLSId s) (leaseTTLRow s (mvcc.api.mvccLeases E.γ)) E (mvcc.api.mvccLeases E.γ)) (fun _ => iprop(|={⊤}=> False))
      ci (akOut who) cd id _ [fun _ => true]) $$ [$Hlt] as %r %err ⟨Hlt, Hr⟩
  · iframe #
    iapply (ttl_attempt_refuted s E (mvcc.api.mvccLeases E.γ) γa who conn _ n ml _ _ hout)
    iframe #
    iintro !> %tok %K %m Hs Hck; iapply Hno $$ Hs Hck
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, %m, %h, %ks, -, -, -, -, -, -, Hf⟩ | ⟨%Herr, -⟩)
  · imod Hf with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  -- `Leases()`
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  have hout : akOut who = akOut who := rfl
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
  (try wp_auto)
  wp_apply (wp_Leases lp conn [addr] (etcdLeaseLeasesSpecMd (srvTLSId s) E (mvcc.api.mvccLeases E.γ)) (fun _ => iprop(|={⊤}=> False))
      ci (akOut who) cd) $$ [$Hlt] as %r %err ⟨Hlt, Hr⟩
  · iframe #
    iapply (leases_attempt_refuted s E (mvcc.api.mvccLeases E.γ) γa who conn _ n ml _ hout)
    iframe #
    iintro !> %tok %K %m Hs Hck; iapply Hno $$ Hs Hck
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, %m, %h, %sl, -, -, -, -, Hf⟩ | ⟨%Herr, -⟩)
  · imod Hf with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  iapply HΦ; iframe Hlt; try itrivial

end proof

end etcd_authlease
end EtcdGrove
end Perennial
