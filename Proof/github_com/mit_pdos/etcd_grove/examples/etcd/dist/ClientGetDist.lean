/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/ClientGetDist.lean`: `cli.Get` through the
`KV` field (`ptr_Get_unfold`) is `(*kv).Get`, whose cross-machine contract is the interim axiom
`KV_Get_dist` (a hypothesis here), at putget's read update after the put fired
(`getAu_of_putGetInvK`); the reply's first key-value from the selection of the one key in the state
the read linearized at (`srvRangeOk_getKey`, `filter_key_of_findKey`). Until 2026-11-25 (O1-B,
`notes/etcd-dist-plan.md` §18.3) an axiom of its own over the published view. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientGetDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Proof.go_etcd_io.etcd.client.v3.KeyOps
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 800000 in
/-- See the file header. -/
theorem Client_Get_dist.wp_proof (wp_KV_Get : KV_Get_dist.spec (GF := GF) (hG := hG)) :
    Client_Get_dist.spec (GF := GF) (hG := hG) := by
  intro π cl ep V Γ mid γf ci cd key val sl hsz
  iintro %Φ ⟨#Pc, Hlt, #Hcl, #Hnp, #Hat, #Hctx, #Hce, #Hopts, #Hinv, #Hlb⟩ HΦ
  ihave #Hms := membersAt_one (Gg := hG.goose_globalGS) ep Γ mid $$ Hat
  ihave ⟨%api, #Hkc⟩ := kvClient_of_new cl [ep] V Γ $$ [Hcl Hnp Hms]
  · iframe #
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  ihave #Hopts' := optsAt_res sl [] iprop(True) $$ Hopts
  -- putget's read update: the state's value of `key` is `val`
  ihave #Hau := getAu_of_putGetInvK Γ.kv γf key val $$ [Hinv Hlb]
  · iframe #
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (wp_KV_Get cl api [ep] V Γ ci cd key sl [] iprop(True)
      (fun σ => iprop(⌜(mvcc.findKey key σ.kvs).map EtcdKv.value = some val⌝))) $$ [Hlt]
    as %resp %err ⟨Hlt, -, Hout⟩
  · (try iframe Hlt)
    iframe #
    isplitl []
    · itrivial
    isplitl []
    · rw [show (opGetModel key []).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    isplitl []
    · ipureintro
      refine ⟨?_, rfl⟩
      unfold opGetPanics opFold OpFull.newOp
      simp
    isplitl []
    · imodintro
      iright
      isplitl []
      · ipureintro; rfl
      iunfold kvReadAu at Hau
      iunfold kvAu at Hau
      iexact Hau
    ipureintro; exact hsz
  iapply HΦ
  iframe Hlt
  have hs : (rangeWireOf (opGetModel key [])).base.serializable = false := rfl
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hs⟩ | %Herr)
  · isimp only [hs, Bool.false_eq_true, ↓reduceIte] at HQ
    icases HQ with %Hv
    ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    ipureintro
    obtain ⟨-, hsel, -⟩ := Hs
    have hrr : σ.readRev (W64 0) = σ.rev := by simp [KVState.readRev]
    have hkvs : (σ.at (σ.readRev (rangeWireOf (opGetModel key [])).base.rev)).kvs = σ.kvs := by
      show (σ.at (σ.readRev (W64 0))).kvs = σ.kvs
      rw [hrr]
      rfl
    rw [hkvs] at hsel
    have h1 := (srvRangeOk_getKey key σ.kvs m.kvs m.more hsel).1
    obtain ⟨kv, hf, hv⟩ : ∃ kv, mvcc.findKey key σ.kvs = some kv ∧ kv.value = val := by
      cases h : mvcc.findKey key σ.kvs with
      | none => rw [h] at Hv; simp at Hv
      | some kv => rw [h] at Hv; simp at Hv; exact ⟨kv, rfl, Hv⟩
    rw [h1, filter_key_of_findKey key σ.kvs (KVState.kvs_sorted σ) kv hf]
    simp [hv]
  · iright
    ipureintro; exact Herr

end proof

end etcd_dist
end EtcdGrove
end Perennial
