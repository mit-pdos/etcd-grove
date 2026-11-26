/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/noAuth.lean`: each of the five calls over
its `Lease_*On_dist` contract at member `mid` (the context's metadata admitted for the client's principal,
`outTokOk_reqMd`, `principalOf cfg = none`); a success carries `mid`'s lease check at a published index `≥ n₀`,
which the caller's premise refutes, so each call errs and `refused` returns. Lean-first (no Rocq counterpart);
F7 stage S5 (the single-process `etcd_authlease.noAuth.wp_proof`'s structure).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.noAuth
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.reqCtx
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.refused
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseGrantOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseRevokeOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseTimeToLiveOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseLeasesOnDist
public import Spec.go_etcd_io.etcd.client.v3.WithAttachedKeys
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthFrozenFloor
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist etcd_dist.authd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 1600000 in
theorem noAuth.wp_proof
    (wp_reqCtx : reqCtx.spec (GF := GF) (hG := hG))
    (wp_refused : refused.spec (GF := GF) (hG := hG))
    (wp_WithAttachedKeys : WithAttachedKeys.spec (GF := GF) (hG := hG))
    (wp_Grant : Lease_GrantOn_dist.spec (GF := GF) (hG := hG))
    (wp_Revoke : Lease_RevokeOn_dist.spec (GF := GF) (hG := hG))
    (wp_TimeToLive : Lease_TimeToLiveOn_dist.spec (GF := GF) (hG := hG))
    (wp_Leases : Lease_LeasesOn_dist.spec (GF := GF) (hG := hG)) :
    noAuth.spec (GF := GF) (hG := hG) := by
  intro π _ _ _ cl who addr id V Γ mid cfg γR L₀ n₀ m₀ Qg Qr Hau Hls Hauth Hrev HγR hP hAs
  wp_start as ⟨Hlt, #Hu, #Hat, #HL0, #Hn0, #Hm0, #HQg, #HQr, #Hno⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave ⟨%lp, #Hlu⟩ := leaseUserAt_of_userCli cl addr V cfg Γ mid $$ [Hu Hat]
  · iframe #
  ihave #Hlu' := Hlu
  iunfold leaseUserAt at Hlu'
  icases Hlu' with ⟨#Hlc, -, %Htok⟩
  iunfold view.leaseClientAt at Hlc
  icases Hlc with ⟨-, -, #Hlf, -⟩
  have hout : outTokOk (principalOf cfg) (reqMd who) := outTokOk_reqMd _ who (fun _ => hP)
  (try wp_auto)
  -- `Grant`
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply (wp_Grant cl lp addr V Γ mid cfg γR L₀ n₀ ci cd (reqMd who) (W64 9000000000) Qg Hau Hls Hauth
      Hrev HγR hout) $$ [$Hlt] as %r %err ⟨Hlt, Hr⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, %mg, -, -, -, -, -, %n, %Hn, -, Hck⟩ | %Herr)
  · imod Hno $$ %n %_ %Hn Hck with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  -- `Revoke(id)`
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply (wp_Revoke cl lp addr V Γ mid cfg γR L₀ n₀ ci cd (reqMd who) id Qr Hau Hauth Hrev HγR hout)
      $$ [$Hlt] as %r %err ⟨Hlt, Hr⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, %mr, -, -, -, %n, %Hn, -, Hck⟩ | %Herr)
  · imod Hno $$ %n %_ %Hn Hck with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  -- `TimeToLive(id)`
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout⟩
  subst Hc
  (try wp_auto)
  ihave #Hnil := leaseOptsAt_nil_d (GF := GF)
  wp_apply (wp_TimeToLive cl lp addr V Γ mid cfg n₀ m₀ ci cd (reqMd who) id slice.nil [] Hau Hls Hauth Hrev
      hout) $$ [$Hlt] as %r %err ⟨Hlt, Hr⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, -, %n, %j, %Hnj, -, -, Hck⟩ | %Herr)
  · imod Hno $$ %n %_ %Hnj.1 Hck with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  -- `TimeToLive(id, WithAttachedKeys())`
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply wp_WithAttachedKeys as %f #Hf
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  ihave #Hopts := leaseOptsAt_one_d (GF := GF) _ f (fun _ => true) $$ [Hslo Hf]
  · iframe #
  (try wp_auto)
  wp_apply (wp_TimeToLive cl lp addr V Γ mid cfg n₀ m₀ ci cd (reqMd who) id _ [fun _ => true] Hau Hls Hauth
      Hrev hout) $$ [$Hlt] as %r %err ⟨Hlt, Hr⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, -, %n, %j, %Hnj, -, -, Hck⟩ | %Herr)
  · imod Hno $$ %n %_ %Hnj.1 Hck with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  -- `Leases()`
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply (wp_Leases cl lp addr V Γ mid cfg n₀ m₀ ci cd (reqMd who) Hau Hls Hauth Hrev hout)
      $$ [$Hlt] as %r %err ⟨Hlt, Hr⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, %ids, %sl, %j, %n, -, -, %Hjn, -, -, Hck⟩ | %Herr)
  · imod Hno $$ %n %_ %Hjn.2 Hck with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  iapply HΦ; iframe Hlt

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
