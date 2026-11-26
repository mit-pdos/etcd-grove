/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/grantPut.lean`: the grant
(`etcd_dist.authd.Lease_GrantOn_dist` at the member the endpoint serves), the caller's step at the granted id,
`clientv3.WithLease`, the put (`KV_PutOn_dist`). Lean-first (no Rocq counterpart); F7 stage S4.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.grantPut
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseGrantOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutOnDist
public import Spec.go_etcd_io.etcd.client.v3.WithLease
public import Perennial.Spec.context.Background
public import Spec.context.WithTimeoutBackgroundMd
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
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

theorem opPutModel_lease_ok' [GooseExts] (k : GoString) (id : w64) :
    ¬ (opPutModel k go!"v" [withLeaseM id]).putPanics ∧ (opPutModel k go!"v" [withLeaseM id]).t = W64 2 := by
  refine ⟨?_, rfl⟩
  simp [opPutModel, OpFull.putPanics, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero]

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
theorem grantPut.wp_proof
    (hWT : context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_WithLease : WithLease.spec (GF := GF) (hG := hG))
    (wp_Grant : Lease_GrantOn_dist.spec (GF := GF) (hG := hG))
    (wp_Put : KV_PutOn_dist.spec (GF := GF) (hG := hG)) :
    grantPut.spec (GF := GF) (hG := hG) := by
  intro π cl addr k V Γ mid cfg γR L₀ n₀ Qg Qp R R' Hau Hls Hauth Hrev HγR hsz hAs
  wp_start as ⟨Hlt, #Hu, #Hat, #HL0, #Hn0, #HQg, HR, HFix⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hms := membersAt_one (Gg := hG.goose_globalGS) addr Γ mid $$ Hat
  ihave ⟨%api, #Huc⟩ := userClientAt_of_userCli cl addr V cfg Γ $$ [Hu Hms]
  · iframe #
  ihave ⟨%lp, #Hlu⟩ := leaseUserAt_of_userCli cl addr V cfg Γ mid $$ [Hu Hat]
  · iframe #
  ihave #Hlu' := Hlu
  iunfold leaseUserAt at Hlu'
  icases Hlu' with ⟨#Hlc, -, %Htok⟩
  iunfold view.leaseClientAt at Hlc
  icases Hlc with ⟨-, -, #Hlf, -⟩
  ihave #Huc' := Huc
  iunfold userClientAt at Huc'
  icases Huc' with ⟨#Hkc, -⟩
  iunfold kvClientAt at Hkc
  icases Hkc with ⟨-, -, #Hkvf, -⟩
  have hP : principalOf cfg = principalOf cfg := rfl
  (try wp_auto)
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -, #Hgout, -⟩
  (try wp_auto)
  wp_apply (wp_Grant cl lp addr V Γ mid cfg γR L₀ n₀ gctx gcd none (W64 9000000000) Qg Hau Hls Hauth Hrev HγR
      (outTokOk_none _)) $$ [$Hlt] as %gr %gerr ⟨Hlt, Hg⟩
  · iframe #
  (try wp_auto)
  wp_apply Hgcancel
  (try wp_auto)
  icases Hg with (⟨%Hgerr, %mg, #Hgid, -, %Hid, ⟨%gi, %gl, Hlv, -⟩, HQgid, -⟩ | %Hgfail)
  rotate_left
  · cases gerr with
    | nil => exact absurd rfl Hgfail.1
    | ok ei =>
      (try wp_auto)
      iapply HΦ; iframe Hlt; ileft; ipureintro; rfl
  subst Hgerr
  (try wp_auto)
  imod HFix $$ %mg.id %Hid HQgid HR with ⟨HR', #Hpu⟩
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
    as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -, #Hpout, -⟩
  (try wp_auto)
  wp_apply wp_WithLease mg.id as %f #Hf
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  ihave #Hopts : optsAt (GF := GF) _ [withLeaseM mg.id] $$ []
  · unfold optsAt
    iexists [f]
    iframe Hslo
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f' %g %Hf' %Hg'
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf' Hg'; subst Hf' Hg'; iexact Hf
    · simp at Hf'
  (try wp_auto)
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  (try wp_auto)
  have hok := opPutModel_lease_ok' k mg.id
  wp_apply (wp_Put cl api [addr] V Γ cfg γR L₀ pctx pcd none k go!"v" _ [withLeaseM mg.id] (Qp mg.id)
      Hauth HγR (outTokOk_none _)) $$ [$Hlt] as %presp %perr ⟨Hlt, Hp⟩
  · iframe #
    ipureintro
    exact ⟨⟨hok.1, hok.2, Or.inr Hrev⟩, hsz mg.id⟩
  (try wp_auto)
  wp_apply Hpcancel
  (try wp_auto)
  icases Hp with (⟨%Hperr, %mp, %σ, -, HQp, -, -, #Hck⟩ | %Hperr)
  · subst Hperr
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    iright
    isplitl []
    · ipureintro; exact ⟨rfl, Hid⟩
    iframe HR' Hck
    isplitl [HQp]
    · iexists σ; iexact HQp
    iexists gi, gl; iexact Hlv
  · cases perr with
    | nil => exact absurd rfl Hperr.1
    | ok ei =>
      (try wp_auto)
      iapply HΦ; iframe Hlt; ileft; ipureintro; rfl

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
