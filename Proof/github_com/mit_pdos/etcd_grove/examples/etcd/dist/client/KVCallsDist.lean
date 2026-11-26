/- Lean-first (no Rocq counterpart).

# `cli.Put`/`cli.Get` of a KV workload across machines, from the interim contracts (#50 N9a)

`notes/etcd-dist-plan.md` §23. `wp_cliPut`/`wp_cliGet`: the promoted methods of `New`'s client (`cli.Put`
with no options, `cli.Get` with any options, at the latest revision, linearizable) at the cluster's view, from
`KV_Put_dist`/`KV_Get_dist` taken as hypotheses (as `Client_Put_dist`/`Client_Get_dist` are proved): the put
with any one-shot update of the put's step, the get with any read update, its answer the server's selection
at the state the update read (`txn.srvRangeOk` at the state's key-values). `optsAt_single`: a one-option
variadic slice.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KVWorkDefs
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

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

/-- **One option** (a variadic slice of one; auth's `optsAt_one`). -/
theorem optsAt_single (sl : GoSlice) (f : GoFunc) (g : OpFull → OpFull) :
    sl ↦*□ [f] ∗ optSpec (GF := GF) f g ⊢ optsAt sl [g] := by
  iintro ⟨#Hsl, #Hf⟩
  iunfold optsAt
  iexists [f]
  iframe Hsl
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %i %f' %g' %Hf' %Hg'
  rcases i with _ | i
  · cases Hf'; cases Hg'; iexact Hf
  · simp at Hf'

set_option maxHeartbeats 800000 in
/-- **`cli.Put(ctx, key, val)` across machines** (see the file header), with a one-shot update `Q` of the
put's step. -/
theorem wp_cliPut (wp_KV_Put : KV_Put_dist.spec (GF := GF) (hG := hG)) [π : NetProtoGS]
    (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key val : GoString)
    (Q : KVState → IProp GF) (hsz : opSizeOk (opPutModel key val [])) (hauth : Γ.auth = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        kvClientAt cl api eps V Γ ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt slice.nil [] ∗
        AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
          <{ etcdKV Γ.kv (kvOpStep (.put (putKeyOp key val)) σ) ∗ ⌜kvRoom σ⌝, COMM Q σ }> }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #slice.nil))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, Q σ) ∨ ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }} := by
  iintro %Φ ⟨#Pc, Hlt, #Hkc, #Hctx, #Hce, #Hopts, Hau⟩ HΦ
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (wp_KV_Put cl api eps V Γ ci cd key val slice.nil [] Q hauth)
    $$ [Hlt Hau] as %resp %err ⟨Hlt, Hout⟩
  · (try iframe Hlt)
    iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl, rfl⟩
      unfold opPutModel OpFull.putPanics opFold OpFull.putInit OpFull.newOp OpModel.zero
      simp
    isplitl [Hau]
    · simp only [show putWireOf (opPutModel key val []) = putKeyOp key val from rfl]
      iexact Hau
    ipureintro; exact hsz
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, %σ, -, HQ, -, -⟩ | %Herr)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists σ
    iexact HQ
  · iright
    ipureintro; exact Herr

set_option maxHeartbeats 800000 in
/-- **`cli.Get(ctx, key, opts...)` across machines** (see the file header), linearizable at the latest
revision, with a read update `Q`: the answer is the server's selection at the state `Q` read. -/
theorem wp_cliGet (wp_KV_Get : KV_Get_dist.spec (GF := GF) (hG := hG)) [π : NetProtoGS]
    (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF)
    (hp : ¬ opGetPanics opts ∧ (opGetModel key opts).t = W64 1)
    (hser : (rangeWireOf (opGetModel key opts)).base.serializable = false)
    (hrev : (rangeWireOf (opGetModel key opts)).base.rev = W64 0)
    (hsz : opSizeOk (opGetModel key opts)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        kvClientAt cl api eps V Γ ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes opts_sl opts R ∗ R ∗
        sortNamesIf (opGetModel key opts).base.sortSet ∗ kvReadAu Γ.kv Q }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #opts_sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ R ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗ □ Q σ ∗
            ⌜txn.srvRangeOk (rangeWireOf (opGetModel key opts)) σ.kvs m.kvs m.more⌝) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }} := by
  iintro %Φ ⟨#Pc, Hlt, #Hkc, #Hctx, #Hce, #Hopts, HR, Hsort, #Hau⟩ HΦ
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (wp_KV_Get cl api eps V Γ ci cd key opts_sl opts R Q) $$ [Hlt HR Hsort]
    as %resp %err ⟨Hlt, HR, Hout⟩
  · (try iframe Hlt)
    iframe HR Hsort
    iframe #
    isplitl []
    · ipureintro; exact hp
    isplitl []
    · imodintro
      iright
      isplitl []
      · ipureintro; exact hser
      iunfold kvReadAu at Hau
      iunfold kvAu at Hau
      iexact Hau
    ipureintro; exact hsz
  iapply HΦ
  iframe Hlt HR
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hs⟩ | %Herr)
  · try isimp only [hser, Bool.false_eq_true, ↓reduceIte] at HQ
    ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m, σ
    iframe Hm HQ
    ipureintro
    obtain ⟨-, hsel, -⟩ := Hs
    have hrr : σ.readRev (W64 0) = σ.rev := by simp [KVState.readRev]
    have hkvs : (σ.at (σ.readRev (rangeWireOf (opGetModel key opts)).base.rev)).kvs = σ.kvs := by
      rw [hrev, hrr]
      rfl
    rw [hkvs] at hsel
    exact hsel
  · iright
    ipureintro; exact Herr

end calls

end etcd_dist_client
end EtcdGrove
end Perennial

end
