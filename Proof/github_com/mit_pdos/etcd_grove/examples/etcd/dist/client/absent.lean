/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/absent.lean`: the request timeout's
context, `root.Get(ctx, k)` (`etcd_dist.authd.KV_GetOn_dist`), whose reply is the read state's key-values of `k`
(`client.srvRangeOk_getKey`), none by the caller's premise. Lean-first (no Rocq counterpart); F7 stage S4.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.absent
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetOnDist
public import Perennial.Spec.context.Background
public import Spec.context.WithTimeoutBackgroundMd
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas
public import Proof.go_etcd_io.etcd.client.v3.KeyOps
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
theorem absent.wp_proof
    (hWT : context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Get : KV_GetOn_dist.spec (GF := GF) (hG := hG)) :
    absent.spec (GF := GF) (hG := hG) := by
  intro π root addr k why V Γ cfg γR L₀ Q Hau Hauth HγR hsz hAs
  wp_start as ⟨Hlt, #Hu, #Hms, #HL0, #HQ, #Hnone⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave ⟨%api, #Huc⟩ := userClientAt_of_userCli root addr V cfg Γ $$ [Hu Hms]
  · iframe #
  ihave #Hu' := Hu
  iunfold userCli at Hu'
  icases Hu' with ⟨-, -, -, %Htok⟩
  ihave #Huc' := Huc
  iunfold userClientAt at Huc'
  icases Huc' with ⟨#Hkc, -⟩
  iunfold kvClientAt at Hkc
  icases Hkc with ⟨-, -, #Hkvf, -⟩
  (try wp_auto)
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
    as %ectx %ecd %ecancel ⟨#Hecancel, #Hectx, #Hece, -, #Hout0, -⟩
  (try wp_auto)
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave Hres := optsAt_res slice.nil [] iprop(True) $$ Hnil
  wp_apply (wp_Get root api [addr] V Γ cfg γR L₀ ectx ecd none k slice.nil [] iprop(True) Q Hau Hauth HγR
      (outTokOk_none _)) $$ [$Hlt $Hres] as %resp %err ⟨Hlt, -, Hout⟩
  · iframe #
    isplitl []
    · rw [show (opGetModel k []).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    ipureintro
    exact ⟨⟨by simp [opGetPanics, opFold, OpFull.newOp, OpModel.zero], rfl, rfl⟩, hsz⟩
  icases Hout with (⟨%Herr, %m, %σ, Hm, #HQσ, %Hs, -⟩ | %Herr)
  rotate_left
  · (try wp_auto)
    wp_apply Hecancel
    cases err with
    | nil => exact absurd rfl Herr.1
    | ok e =>
      (try wp_auto)
      iapply HΦ; iframe Hlt; ileft; ipureintro; rfl
  subst Herr
  (try wp_auto)
  wp_apply Hecancel
  (try wp_auto)
  ihave %Hk := Hnone $$ %σ HQσ
  have Hkv : m.kvs = [] := by
    obtain ⟨-, hsel, -⟩ := Hs
    have hrr : σ.readRev (W64 0) = σ.rev := by simp [KVState.readRev]
    have hkvs : (σ.at (σ.readRev (W64 0))).kvs = σ.kvs := by
      rw [hrr]
      rfl
    try rw [show (rangeWireOf (opGetModel k [])).base.rev = W64 0 from rfl] at hsel
    rw [hkvs] at hsel
    have h1 := (srvRangeOk_getKey k σ.kvs m.kvs m.more hsel).1
    rw [h1, List.filter_eq_nil_iff]
    intro v hv
    simpa using Hk v hv
  iunfold rangeRespMsg at Hm
  icases Hm with ⟨%Hnn, %h, %sl, %kvps, #Hh, #Hhf, #Hkvf', #Hsl, #Hkvs, #Hmore, #Hcount⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hlen', -⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have Hz : sl.len = W64 0 := by
    have hl := Hsll.1
    rw [Hlen', Hkv] at hl
    simp at hl
    word
  (try wp_auto)
  simp only [Hz]
  (try wp_auto)
  iapply HΦ; iframe Hlt; iright
  isplitl []
  · ipureintro; rfl
  iexists σ; iexact HQσ

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
