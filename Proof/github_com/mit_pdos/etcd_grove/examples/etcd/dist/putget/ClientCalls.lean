/- Lean-first (no Rocq counterpart).

# putget's `cli.Put`/`cli.Get` across machines (`notes/putget-dist-plan.md` §12; stage B′, 2026-11-28)

`New`'s client of a member of an auth-off view `Γ` (`etcdAddrAt`), under putget's invariant at the view's
KV names (`putGetInvK`): `cli.Put` through the `KV` field (`ptr_Put_unfold`) is `(*kv).Put`, by
`kv.Put.spec` at the client's `isKv` (`isKv_of_kvClientAt`) with putget's put update fired at most once
(`putAu_of_putGetInvK`, `kvOpAu_one`), its `nil` reply the put's flag; `cli.Get` likewise by `kv.Get.spec`
with putget's read update after the put fired (`getAu_of_putGetInvK`), the reply's first key-value from the
selection of the one key in the state the read linearized at (`srvRangeOk_getKey`, `filter_key_of_findKey`).
(Until stage B′ the theorems `etcd_dist.Client_Put_dist`/`Client_Get_dist`, over the interim axioms
`KV_Put_dist`/`KV_Get_dist`.)
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Put
public import Spec.go_etcd_io.etcd.client.v3.kv__Get
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
namespace etcd_putget_dist

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist

section calls
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 800000 in
/-- **putget's `cli.Put(ctx, key, val)` across machines** (see the file header); on `nil`, the put's flag. -/
theorem wp_pgPut (wp_KV_Put : kv.Put.spec (GF := GF) (hG := hG)) :
  ∀ [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (γf : GName) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice),
  opSizeOk (opPutModel key val []) → Γ.auth = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      isNewClient cl [ep] V ∗ clientNoProxy cl ∗ etcdAddrAt (Gg := hG.goose_globalGS) ep Γ mid ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ putGetInvK Γ.kv γf key val }}
    (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
        go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ monoNatLbOwn γf 1) ∨ ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }} := by
  intro π cl ep V Γ mid γf ci cd key val sl hsz hauth
  iintro %Φ ⟨#Pc, Hlt, #Hcl, #Hnp, #Hat, #Hctx, #Hce, #Hopts, #Hinv⟩ HΦ
  ihave #Hms := membersAt_one (Gg := hG.goose_globalGS) ep Γ mid $$ Hat
  ihave ⟨%api, #Hkc⟩ := kvClient_of_new cl [ep] V Γ $$ [Hcl Hnp Hms]
  · iframe #
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  ihave #Hkv := isKv_of_kvClientAt cl api [ep] V Γ hauth $$ Hkc
  -- putget's put update, fired at most once (`Γ.auth = false`: the put is sent at most once)
  ihave #Hau := putAu_of_putGetInvK Γ.kv γf key val $$ Hinv
  ihave Hau1 := kvOpAu_one Γ.kv (.put (putKeyOp key val)) (fun _ => monoNatLbOwn γf 1) $$ Hau
  iunfold kvOpAu1 at Hau1
  iunfold kvAu1 at Hau1
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (wp_KV_Put api Γ.kv false ci cd key val sl [] (fun _ => iprop(□ monoNatLbOwn γf 1)))
    $$ [Hlt Hau1] as %resp %err ⟨Hlt, Hout⟩
  · (try iframe Hlt)
    iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl, rfl⟩
      unfold opPutModel OpFull.putPanics opFold OpFull.putInit OpFull.newOp OpModel.zero
      simp
    isplitl [Hau1]
    · simp only [show putWireOf (opPutModel key val []) = putKeyOp key val from rfl]
      iexact Hau1
    ipureintro; exact hsz
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, %σ, -, #HQ, -, -⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexact HQ
  · iright
    ipureintro; exact Herr

set_option maxHeartbeats 800000 in
/-- **putget's `cli.Get(ctx, key)` across machines** (see the file header); on `nil`, the reply's first
key-value holds `val`. -/
theorem wp_pgGet (wp_KV_Get : kv.Get.spec (GF := GF) (hG := hG)) :
  ∀ [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (γf : GName) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice),
  opSizeOk (opGetModel key []) → Γ.auth = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      isNewClient cl [ep] V ∗ clientNoProxy cl ∗ etcdAddrAt (Gg := hG.goose_globalGS) ep Γ mid ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
      putGetInvK Γ.kv γf key val ∗ monoNatLbOwn γf 1 }}
    (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
        go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
          ⌜m.kvs.head?.map EtcdKv.value = some val⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }} := by
  intro π cl ep V Γ mid γf ci cd key val sl hsz hauth
  iintro %Φ ⟨#Pc, Hlt, #Hcl, #Hnp, #Hat, #Hctx, #Hce, #Hopts, #Hinv, #Hlb⟩ HΦ
  ihave #Hms := membersAt_one (Gg := hG.goose_globalGS) ep Γ mid $$ Hat
  ihave ⟨%api, #Hkc⟩ := kvClient_of_new cl [ep] V Γ $$ [Hcl Hnp Hms]
  · iframe #
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  ihave #Hkv := isKv_of_kvClientAt cl api [ep] V Γ hauth $$ Hkc
  ihave #Hopts' := optsAt_res sl [] iprop(True) $$ Hopts
  -- putget's read update: the state's value of `key` is `val`
  ihave #Hau := getAu_of_putGetInvK Γ.kv γf key val $$ [Hinv Hlb]
  · iframe #
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (wp_KV_Get api Γ.kv false ci cd key sl [] iprop(True)
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
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hs⟩ | ⟨%Herr, -⟩)
  · try isimp only [hs, Bool.false_eq_true, ↓reduceIte] at HQ
    icases HQ with %Hv
    ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    ipureintro
    obtain ⟨-, hsel, -⟩ := Hs
    have hrr : σ.readRev (W64 0) = σ.rev := by simp [KVState.readRev]
    have hkvs : (σ.at (σ.readRev (W64 0))).kvs = σ.kvs := by
      rw [hrr]
      rfl
    try rw [show (rangeWireOf (opGetModel key [])).base.rev = W64 0 from rfl] at hsel
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

end calls

end etcd_putget_dist
end EtcdGrove
end Perennial

end
