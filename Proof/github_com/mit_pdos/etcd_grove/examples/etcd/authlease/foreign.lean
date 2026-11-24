/-
Proof of `Spec/.../authlease/foreign.lean` (auth-lease S4, item 9, checks 3–5). Lean-first (no Rocq
counterpart). `Revoke(id)`'s success carries, with auth on, the caller's result `Qr` (refuted with `R`); `TimeToLive`
with keys and `Leases` carry, at the token of one of their attempts (`akTokSeen`), the passed check over
`id`'s keys from `m` on, or over the keys of every lease of a listing at an index from `m` on (refuted
with `R`). So each call errs, `refused` returns, and `R` is kept.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.foreign
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.reqCtx
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.refused
public import Spec.go_etcd_io.etcd.client.v3.lessor__Revoke
public import Spec.go_etcd_io.etcd.client.v3.lessor__TimeToLive
public import Spec.go_etcd_io.etcd.client.v3.lessor__Leases
public import Spec.go_etcd_io.etcd.client.v3.WithAttachedKeys
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.LeaseAttempts
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

theorem foreign.wp_proof
    (wp_reqCtx : reqCtx.spec (GF := GF) (hG := hG))
    (wp_refused : refused.spec (GF := GF) (hG := hG))
    (wp_Revoke : lessor.Revoke.spec (GF := GF) (hG := hG))
    (wp_TimeToLive : lessor.TimeToLive.spec (GF := GF) (hG := hG))
    (wp_Leases : lessor.Leases.spec (GF := GF) (hG := hG))
    (wp_WithAttachedKeys : WithAttachedKeys.spec (GF := GF) (hG := hG)) :
    foreign.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS CRE CEC cli who addr id s E ρ γa n m Qr R hwho hon hAs
  wp_start as ⟨#Htk, #Hsv, #Hn, #Hm, HR, #HQr, #HnoR, #HnoT, #HnoL⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Htk0 := Htk
  iunfold clientTokAt at Htk0
  icases Htk0 with ⟨%api, %conn, -, -, #Htok, -, -, %lp, #Hlf, #Hrem⟩
  iunfold etcdstart.etcdLeaseServedOn at Hsv
  icases Hsv with ⟨-, #HrR, #HrT, #HrL⟩
  (try wp_auto)
  -- `Revoke(id)`: its success has `Qr`
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  have hout : akOut who = akOut who := rfl
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
  (try wp_auto)
  wp_apply (wp_Revoke lp conn [addr] (etcdLeaseRevokeSpecOn (srvTLSId s) E ρ) _
      ci (akOut who) cd id) as %r %err Hr
  · iframe #
    iapply (revoke_attempt s E ρ conn _ n id Qr (fun _ => iprop(∃ σ, Qr σ)))
    iframe #
    isplitl []
    · iintro !>
      iapply HQr
      · iexact Htok
      · ipureintro; exact hout
    iintro !> %md %m' - Hres -
    iunfold v3rpc.leaseRevokeResT at Hres
    ihave Hres := Hres $$ %hon
    icases Hres with ⟨%hm, %L, -, -, -, HQ⟩
    iexists _; iexact HQ
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, %m', -, ⟨%σ, HQ⟩⟩ | ⟨%Herr, -⟩)
  · iapply fupd_wp
    imod HnoR $$ HQ HR with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  -- `TimeToLive(id, WithAttachedKeys())`: its success has the check over `id`'s keys
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
  wp_apply (wp_TimeToLive lp conn [addr] (etcdLeaseTTLSpecMd (srvTLSId s) (leaseTTLRow s (mvcc.api.mvccLeases E.γ)) E (mvcc.api.mvccLeases E.γ))
      (fun _ => iprop(∃ tok : Option GoString, akTokSeen γa who tok ∗
        leaseCheckFrom (srvTLSId s) E tok n (fun info =>
          leaseKeysVerdictFrom E.authMode n info (mvcc.api.mvccLeases E.γ) m id .read))) ci (akOut who) cd id _ [fun _ => true])
    as %r %err Hr
  · iframe #
    iapply (ttl_attempt_seen s E (mvcc.api.mvccLeases E.γ) γa who conn _ n m (id, leaseKeysFold [fun _ => true] false) _ hout)
    iframe #
    iintro !> %r' %tok #Hs #Hck
    iexists tok
    iframe Hs
    have hk : leaseKeysFold [fun _ => true] false = true := rfl
    isimp only [hk, ↓reduceIte] at Hck
    iexact Hck
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, %m', %h, %ks, -, -, -, -, -, -, ⟨%tok, #Hs, #Hck⟩⟩ | ⟨%Herr, -⟩)
  · iapply fupd_wp
    imod HnoT $$ Hs Hck HR with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  -- `Leases()`: its success has the check over the listing's keys
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  have hout : akOut who = akOut who := rfl
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
  (try wp_auto)
  wp_apply (wp_Leases lp conn [addr] (etcdLeaseLeasesSpecMd (srvTLSId s) E (mvcc.api.mvccLeases E.γ))
      (fun r => iprop(∃ (tok : Option GoString) (i : Nat), ⌜m ≤ i⌝ ∗ akTokSeen γa who tok ∗
        lease.leaseIdsAt (mvcc.api.mvccLeases E.γ) i r.ids ∗
        leaseCheckFrom (srvTLSId s) E tok n (fun info => iprop([∗list] id' ∈ r.ids,
          leaseKeysVerdictFrom E.authMode n info (mvcc.api.mvccLeases E.γ) i id' .read)))) ci (akOut who) cd) as %r %err Hr
  · iframe #
    iapply (leases_attempt_seen s E (mvcc.api.mvccLeases E.γ) γa who conn _ n m _ hout)
    iframe #
    iintro !> %r' %tok %i %hi #Hs #Hids #Hck
    iexists tok, i
    iframe Hs Hids Hck
    ipureintro; exact hi
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, %m', %h, %sl, -, -, -, -, ⟨%tok, %i, %hi, #Hs, #Hids, #Hck⟩⟩ | ⟨%Herr, -⟩)
  · iapply fupd_wp
    imod HnoL $$ %tok %i %(m'.ids) %hi Hs Hids Hck HR with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  iapply HΦ; iexact HR

end proof

end etcd_authlease
end EtcdGrove
end Perennial
