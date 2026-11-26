/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/foreign.lean`: the one call, `Revoke`,
over its `Lease_RevokeOn_dist` contract at member `mid` (the context's metadata admitted for the client's
principal, `outTokOk_reqMd`); a success is refuted by the caller's premise with `R`, so the call errs and
`refused` returns. Lean-first (no Rocq counterpart); F7 stage S5 (the single-process `etcd_authlease.foreign.wp_proof`'s
structure).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.foreign
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.reqCtx
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.refused
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseRevokeOnDist
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

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
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
theorem foreign.wp_proof
    (wp_reqCtx : reqCtx.spec (GF := GF) (hG := hG))
    (wp_refused : refused.spec (GF := GF) (hG := hG))
    (wp_Revoke : Lease_RevokeOn_dist.spec (GF := GF) (hG := hG)) :
    foreign.spec (GF := GF) (hG := hG) := by
  intro π _ _ _ cl who addr id V Γ mid cfg γR L₀ n₀ Qr R Hau Hauth Hrev HγR hP hAs
  wp_start as ⟨Hlt, #Hu, #Hat, #HL0, #Hn0, HR, #HQr, #HnoR⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave ⟨%lp, #Hlu⟩ := leaseUserAt_of_userCli cl addr V cfg Γ mid $$ [Hu Hat]
  · iframe #
  ihave #Hlu' := Hlu
  iunfold leaseUserAt at Hlu'
  icases Hlu' with ⟨#Hlc, -, %Htok⟩
  iunfold view.leaseClientAt at Hlc
  icases Hlc with ⟨-, -, #Hlf, -⟩
  have hout : outTokOk (principalOf cfg) (reqMd who) := outTokOk_reqMd _ who hP
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
  icases Hr with (⟨-, %mr, -, ⟨%σ, HQ⟩, #Hwc, -⟩ | %Herr)
  · iapply fupd_wp
    imod HnoR $$ %σ HQ Hwc HR with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  iapply HΦ; iframe Hlt HR

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
