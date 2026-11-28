/- Lean-first (no Rocq counterpart).

# `cli.Put`/`cli.Get`/`cli.Compact` of the compact workload across machines (#50 F5)

`notes/etcd-dist-plan.md` §26. The promoted methods of `New`'s client at the cluster's view, from the client
specs `kv.Put.spec`/`kv.Get.spec`/`kv.Compact.spec` taken as hypotheses, at the client's `isKv` of an auth-off
view (`isKv_of_kvClientAt`), keeping what compact's checks read: the put's reply revision and the revision
reached (`kvRevLb`), the get's selection at the revision it asks (any options) and its reply revision.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Put
public import Spec.go_etcd_io.etcd.client.v3.kv__Get
public import Spec.go_etcd_io.etcd.client.v3.kv__Compact
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CompactWorkDefs
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

set_option maxHeartbeats 800000 in
/-- **`cli.Put(ctx, key, val)` across machines**, with a one-shot update `Q` of the put's step; on `nil` the
reply's revision, the state's next, reached. -/
theorem wp_cliPutR (wp_Put : kv.Put.spec (GF := GF) (hG := hG)) [π : NetProtoGS]
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
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
            ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧ kvRevFits (σ.rev + 1)⌝ ∗
            kvRevLb Γ.kv m.hdr.revision) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }} := by
  iintro %Φ ⟨#Pc, Hlt, #Hkc, #Hctx, #Hce, #Hopts, Hau⟩ HΦ
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  ihave #Hkv := isKv_of_kvClientAt cl api eps V Γ hauth $$ Hkc
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (wp_Put api Γ.kv false ci cd key val slice.nil [] Q)
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
  icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hs, #Hrv⟩ | Herr)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m, σ
    iframe Hm HQ Hrv
    ipureintro; exact ⟨Hs.1, Hs.2.2.1⟩
  · iright
    icases Herr with ⟨%Herr, -⟩
    ipureintro; exact Herr

set_option maxHeartbeats 800000 in
/-- **`cli.Get(ctx, key, opts...)` across machines**, linearizable, with a read update `Q`: the answer is the
server's selection at the revision asked of the state `Q` read, and the reply's revision the state's. -/
theorem wp_cliGetR (wp_Get : kv.Get.spec (GF := GF) (hG := hG)) [π : NetProtoGS]
    (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF)
    (hp : ¬ opGetPanics opts ∧ (opGetModel key opts).t = W64 1)
    (hser : (rangeWireOf (opGetModel key opts)).base.serializable = false)
    (hsz : opSizeOk (opGetModel key opts)) (hauth : Γ.auth = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        kvClientAt cl api eps V Γ ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes opts_sl opts R ∗ R ∗
        sortNamesIf (opGetModel key opts).base.sortSet ∗ kvReadAu Γ.kv Q }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #opts_sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ R ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗ □ Q σ ∗
            ⌜txn.srvRangeOk (rangeWireOf (opGetModel key opts))
                (σ.at (σ.readRev (rangeWireOf (opGetModel key opts)).base.rev)).kvs m.kvs m.more ∧
              m.hdr.revision = W64 (σ.rev : Int) ∧ kvRevFits σ.rev⌝) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }} := by
  iintro %Φ ⟨#Pc, Hlt, #Hkc, #Hctx, #Hce, #Hopts, HR, Hsort, #Hau⟩ HΦ
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  ihave #Hkv := isKv_of_kvClientAt cl api eps V Γ hauth $$ Hkc
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (wp_Get api Γ.kv false ci cd key opts_sl opts R Q) $$ [Hlt HR Hsort]
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
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hs⟩ | ⟨%Herr, -⟩)
  · have hser' : (opGetModel key opts).base.serializable = false := by
      first
      | exact hser
      | simpa [rangeWireOf] using hser
    try isimp only [hser, hser', Bool.false_eq_true, ↓reduceIte] at HQ
    ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m, σ
    iframe Hm HQ
    ipureintro
    exact ⟨Hs.2.1, Hs.2.2.2.1, Hs.2.2.2.2.1⟩
  · iright
    ipureintro; exact Herr

set_option maxHeartbeats 800000 in
/-- **`cli.Compact(ctx, rev)` across machines**, the cluster in compaction mode, the caller knowing the KV has
reached `rev` plus the retention; its outcome is not read. -/
theorem wp_cliCompact (wp_Compact : kv.Compact.spec (GF := GF) (hG := hG)) [π : NetProtoGS]
    (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (rev : w64)
    (hrev : 1 ≤ sint.Z rev) (hcmp : Γ.kv.cmp = true) (hauth : Γ.auth = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        kvClientAt cl api eps V Γ ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
        kvRevLbZ Γ.kv (sint.Z rev + Γ.kv.cret) }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Compact")) (Val #(GoInterface.ok ci))) (Val #rev)) (Val #slice.nil))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 }} := by
  iintro %Φ ⟨#Pc, Hlt, #Hkc, #Hctx, #Hce, #Hlb⟩ HΦ
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  ihave #Hkv := isKv_of_kvClientAt cl api eps V Γ hauth $$ Hkc
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Compact_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (wp_Compact api Γ.kv false ci cd rev hrev hcmp) $$ [Hlt] as %resp %err ⟨Hlt, -⟩
  · (try iframe Hlt)
    iframe #
  iapply HΦ
  iframe Hlt

end calls

end etcd_dist_client
end EtcdGrove
end Perennial

end
