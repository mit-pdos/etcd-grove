/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/barrier.lean`: root's client
(`newUserClient.spec`), the request timeout's context (no outgoing metadata), `root.Get(ctx, "z/barrier")`
(`etcd_dist.authd.KV_GetOn_dist`, with no read update: its check `readCheckedD` gives the floor), the cancel, and
the deferred `Close`. Lean-first (no Rocq counterpart); F7 stage S4.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.barrier
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newUserClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetOnDist
public import Spec.go_etcd_io.etcd.client.v3.Client__Close
public import Perennial.Spec.context.Background
public import Spec.context.WithTimeoutBackgroundMd
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas
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
theorem barrier.wp_proof
    (wp_newUserClient : newUserClient.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Get : KV_GetOn_dist.spec (GF := GF) (hG := hG))
    (wp_Close : EtcdGrove.Client.Close.spec (GF := GF) (hG := hG)) :
    barrier.spec (GF := GF) (hG := hG) := by
  intro π addr V Γ γR L₀ Htb Hpe hAs Hau Hauth HγR
  wp_start as ⟨Hlt, #Hms, #HL0⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (wp_newUserClient addr go!"root" go!"root-pw" V Γ Htb Hpe (by unfold strsSizeOk; decide)
      (by decide) (by decide) Hau Hauth) $$ [$Hlt] as %rcl %rerr ⟨Hlt, Hrc⟩
  · iframe #
  icases Hrc with (⟨%Hrerr, %cfg, #Hu, %Hprin⟩ | %Hrfail)
  rotate_left
  · obtain ⟨Hrerr, -⟩ := Hrfail
    cases rerr with
    | nil => exact absurd rfl Hrerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; iframe Hlt; ileft; ipureintro; rfl
  subst Hrerr
  ihave ⟨%api, #Huc⟩ := userClientAt_of_userCli rcl addr V cfg Γ $$ [Hu Hms]
  · iframe #
  ihave #Hu' := Hu
  iunfold userCli at Hu'
  icases Hu' with ⟨#Hnc, #Hnp, -, -⟩
  ihave #Hcore := clientCoreAt_of_new rcl [addr] V $$ [Hnc Hnp]
  · iframe #
  ihave #Huc' := Huc
  iunfold userClientAt at Huc'
  icases Huc' with ⟨#Hkc, -⟩
  iunfold kvClientAt at Hkc
  icases Hkc with ⟨-, -, #Hkvf, -⟩
  (try wp_auto)
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
    as %ectx %ecd %ecancel ⟨#Hecancel, #Hectx, #Hece, -, #Hnone, -⟩
  (try wp_auto)
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave Hres := optsAt_res slice.nil [] iprop(True) $$ Hnil
  wp_apply (wp_Get rcl api [addr] V Γ cfg γR L₀ ectx ecd none go!"z/barrier" slice.nil [] iprop(True)
      (fun _ => iprop(True)) Hau Hauth HγR (by rw [Hprin]; left; rfl)) $$ [$Hlt $Hres]
    as %resp %err ⟨Hlt, -, Hout⟩
  · iframe #
    isplitl []
    · itrivial
    isplitl []
    · rw [show (opGetModel go!"z/barrier" []).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    isplitl []
    · ipureintro; exact ⟨by simp [opGetPanics, opFold, OpFull.newOp, OpModel.zero], rfl, rfl⟩
    isplitl []
    · imodintro; ileft; ipureintro; rfl
    ipureintro
    exact opSizeOk_opGetModel (K := 16) (E := 0) (V := 0) (optsKeep_nil _ _ _) (by decide) (by decide)
  icases Hout with (⟨%Herr, %m, %σ, -, -, -, Hck⟩ | %Herr)
  · (try wp_auto)
    wp_apply Hecancel
    subst Herr
    (try wp_auto)
    wp_apply wp_Close as %ce -
    · iframe #
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    iright
    isplitl []
    · ipureintro; rfl
    iunfold readCheckedD at Hck
    icases Hck with ⟨%mid, %info, %mm, %L, Hsv, -, -, -, Hfl⟩
    iunfold servedBy at Hsv
    icases Hsv with ⟨%a, %Ha, Hat⟩
    simp only [List.mem_singleton] at Ha
    subst Ha
    iunfold barrierFloor
    iexists mid, mm
    iframe Hat Hfl
  · (try wp_auto)
    wp_apply Hecancel
    cases err with
    | nil => exact absurd rfl Herr.1
    | ok e =>
      (try wp_auto)
      wp_apply wp_Close as %ce -
      · iframe #
      (try wp_auto)
      iapply HΦ
      iframe Hlt
      ileft
      ipureintro; rfl

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
