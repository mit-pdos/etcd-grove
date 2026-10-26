/-
**A client of etcd's KV meets the clients' get contracts** (D48, 2026-10-26). Lean-first, no
Rocq counterpart.

`kv_get_km`: a `*kv` of etcd's KV `γ.kv` (`isKv`, any `dup`), with the adapter's invariant
(`kmInv γ`, `EtcdModelKV.lean`), answers a linearizable exact get as `kvGetResultC` and
`getRespMore` say at the adapter's model (`etcdModelOfKV γ`), for a non-empty prefix: the call is
`kv.Get.spec`'s, with the adapter's read update after the floor the caller knows (`km_read_au` at
`km_reached_lb`'s changes); its reply's state `σ`, a well-formed log's (`kvLogOk`), is one the
client saw, so etcd's state at its revision is `σ`'s log's last, as the server's model said
(`ServerKVGet.lean`'s `wire_answer`, `prefix_answer`). `isEtcdKVE_of_km`, `isEtcdKVTodo_of_km`:
the cache's and the recipes' contracts from it.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ServerKVGet
public import Proof.go_etcd_io.etcd.client.v3.EtcdModelKV
public import Proof.go_etcd_io.etcd.client.v3.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil errStrOk_of_statusErrOk)

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A `*kv`'s linearizable exact get at the adapter's model** (see the file header). -/
theorem kv_get_km (api : Loc) (γ : KMNames) (dup : Bool) (pfx : GoString) (hpfx : pfx ≠ [])
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) (lo : w64)
    (Hnp : ¬ opGetPanics gs) (Ht : (opGetModel key gs).t = W64 1)
    (Hx : (opGetModel key gs).getExact)
    (Hlin : (opGetModel key gs).base.serializable = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv api γ.kv dup ∗
        kmInv γ ∗ sortNamesIf (opGetModel key gs).base.sortSet ∗ ctxOk ci cd ∗
        ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗ etcdReached (EM := etcdModelOfKV γ) lo }}
      (App (App (App (Val #(methods (kvIfaceOf api).ty go!"Get" (kvIfaceOf api).v))
        (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        R ∗ kvGetResultC (EM := etcdModelOfKV γ) pfx lo (opGetModel key gs) resp err ∗
        getRespMore (EM := etcdModelOfKV γ) pfx (opGetModel key gs) resp err ∗
        statusErrOk err }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hinv, #Hsi, #Hctx, #Hce, #Hopts, HR, #Hlo⟩ HΦ
  have hws : (rangeWireOf (opGetModel key gs)).base.serializable = false := by
    rw [(wire_fields _).2.2.2.2.2.2.1]; exact Hlin
  -- the floor: changes the client saw, `lo` of them or more, and the read update after them
  imod km_reached_lb γ lo $$ Hlo with ⟨%l0, #Hl0, %Hll⟩
  ihave #Hau := km_read_au γ l0 $$ [$Hinv $Hl0]
  iapply (v3.kv.wp_Get api γ.kv dup ci cd key sl gs R (kmSeenQ γ l0)) $$ [HR]
  · iframe #
    iframe
    isplitl []
    · ipureintro; exact ⟨Hnp, Ht⟩
    imodintro
    iright
    isplitl []
    · ipureintro; exact hws
    iunfold kvReadAu at Hau
    iunfold kvAu at Hau
    iexact Hau
  inext
  iintro %resp %err ⟨HR, Hout⟩
  iapply HΦ
  iframe HR
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hs⟩ | ⟨%Herr, #Hke⟩)
  rotate_left
  · iunfold kvErr at Hke
    icases Hke with ⟨-, #Hse, -⟩
    isplitl
    · unfold kvGetResultC; ileft; ipureintro; exact Herr.1
    isplitl
    · unfold getRespMore; ileft; ipureintro; exact Herr.1
    iexact Hse
  simp only [hws, Bool.false_eq_true, ↓reduceIte]
  iunfold kmSeenQ at HQ
  icases HQ with ⟨#Hlb, %Hpre⟩
  obtain ⟨hrle, hsrv, -, hrev, h3, hok⟩ := Hs
  have hrc := kvLogOk_rev σ hok
  have hkvs := kvLogOk_kvs σ hok
  have hfl : sint.Z lo ≤ (σ.rev : Int) := by have := Hpre.length_le; omega
  ihave ⟨#Hreach, #Hra⟩ := km_reached_of γ σ.changes σ.rev (by omega) (by omega) $$ Hlb
  ihave ⟨#Hst, %Hwf⟩ := km_etcdState_last γ σ pfx hok $$ Hlb
  iunfold rangeRespMsg at Hm
  icases Hm with ⟨%Hrn, %h, %ksl, %ps, #Hh, #Hhf, #Hksl, #Hps, #Hkvs, #Hmore, -⟩
  iunfold hdrFull at Hhf
  icases Hhf with ⟨%Hhn, -, -, #Hrev, -, -⟩
  rw [hrev]
  ihave #Hgr : getRespRev resp (W64 (σ.rev : Int)) $$ []
  · unfold getRespRev
    iexists h
    iframe #
    ipureintro; exact Hhn
  have hst : (opGetModel key gs).base.rev = W64 0 →
      (σ.at (σ.readRev (rangeWireOf (opGetModel key gs)).base.rev)).kvs = mvcc.stateAfter σ.log := by
    intro h0
    rw [(wire_fields _).2.2.1, h0]
    simp only [KVState.readRev, show sint.Z (W64 0) = 0 from rfl, Int.le_refl, ↓reduceIte]
    exact hkvs
  generalize opGetModel key gs = o at Hx hst hsrv hfl Hlin ⊢
  isplitl
  · unfold kvGetResultC
    iright
    isplitl; · ipureintro; exact Herr
    iexists (W64 (σ.rev : Int))
    iframe Hgr Hreach
    isplitr
    · rw [etcdModelOfKV_etcdReadAt]; iexact Hra
    isplitr
    · unfold etcdHasState
      iexists (txn.underPfx pfx (mvcc.stateAfter σ.log))
      rw [etcdModelOfKV_etcdState]
      iexact Hst
    isplitl
    · ipureintro
      have : sint.Z (W64 (σ.rev : Int)) = σ.rev := by word
      refine ⟨fun _ => by rw [this]; exact hfl, by omega⟩
    ihave #Hpk := kvPtrsAt_of_kvsIs ps m.kvs $$ Hkvs
    split
    · rename_i hp
      have h0 := isPrefixGet_rev pfx o hp
      have ha := wire_answer o Hx _ _ _ hsrv
      rw [hst h0] at ha
      obtain ⟨hkv, -, -⟩ := prefix_answer pfx o hp hpfx _ _ ha.1
      iunfold txn.kvsIs at Hkvs
      icases Hkvs with ⟨%Hlen, #Hall⟩
      iexists ((m.kvs.map EtcdKv.key).zip ps)
      isplitl
      · unfold isEtcdKvs
        iexists (txn.underPfx pfx (mvcc.stateAfter σ.log))
        rw [etcdModelOfKV_etcdState]
        iframe Hst
        isplitl
        · ipureintro
          rw [← hkv, List.map_fst_zip (by simp; omega)]
        isplitl
        · ipureintro; exact Hwf
        unfold kvValsAt
        iintro !> %i %e %w %He %Hw
        rw [← hkv] at Hw
        have h1 := zip_getElem?_snd _ _ i e He
        ihave Hkw := Hall $$ %i %e.2 %w %h1 %Hw
        unfold kvValAt; iunfold txn.kvIs at Hkw; iexact Hkw
      · unfold getRespKvs
        iexists ksl
        iframe Hksl
        rw [List.map_snd_zip (by simp; omega)]
        iexact Hps
    · unfold getRespRange
      split
      · rename_i hc
        have ha := wire_answer o Hx _ _ _ hsrv
        rw [hst hc.1] at ha
        iexists (txn.underPfx pfx (mvcc.stateAfter σ.log)), ksl, ps, m.kvs
        rw [etcdModelOfKV_etcdState]
        iframe #
        ipureintro
        refine ⟨Hwf, ?_⟩
        rw [v3rpc.rangeSel_underPfx pfx _ o hc.2]
        exact ha.1
      · itrivial
  isplitl
  · unfold getRespMore
    iright
    iexists (W64 (σ.rev : Int)), m.more
    iframe Hgr Hmore
    split
    · rename_i hc
      have ha := wire_answer o Hx _ _ _ hsrv
      rw [hst hc.1] at ha
      iexists (txn.underPfx pfx (mvcc.stateAfter σ.log))
      rw [etcdModelOfKV_etcdState]
      iframe Hst
      ipureintro
      rw [v3rpc.rangeSel_underPfx pfx _ o hc.2]
      exact ha.2
    · itrivial
  rw [Herr]
  iapply statusErrOk_nil

/-- **A client of etcd's KV meets the recipes' get contract** (`isEtcdKVTodo`) at the adapter's
model, for a non-empty prefix: `kv_get_km` at `context.TODO()` (`todo_ctx`, given that
`errors.As` can take `*rpctypes.EtcdError`, `hAs`). -/
theorem isEtcdKVTodo_of_km (api : Loc) (γ : KMNames) (dup : Bool) (pfx : GoString)
    (hpfx : pfx ≠ [])
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv api γ.kv dup ∗
        kmInv γ ∗ sortNamesOk ⊢
      isEtcdKVTodo (EM := etcdModelOfKV γ) (kvIfaceOf api) pfx := by
  iintro ⟨#Pc, #Hkv, #Hinv, #Hsn⟩
  unfold isEtcdKVTodo
  iintro !> %key %sl %gs %R %lo %Φ !> ⟨#Hopts, HR, #Hlo, %Hpre⟩ HΦ
  obtain ⟨Hnp, Ht, Hx, Hlin⟩ := Hpre
  imod (todo_ctx (GF := GF) hAs) with ⟨%cd, #Hctx, #Hce⟩
  ihave #Hsi := sortNamesIf_of_ok (opGetModel key gs).base.sortSet $$ Hsn
  iapply (kv_get_km api γ dup pfx hpfx todoCtxVal cd key sl gs R lo Hnp Ht Hx Hlin)
    $$ [HR] [HΦ]
  · iframe #; iframe
  inext
  iintro %resp %err ⟨HR, #Hres, #Hmore, -⟩
  iapply HΦ
  iframe HR Hmore
  iapply (kvGetResultC_R (EM := etcdModelOfKV γ)) $$ Hres

/-- **A client of etcd's KV meets the cache's get contract** (`isEtcdKVE`) at the adapter's
model, for a non-empty prefix: `kv_get_km` at any context (`ctxErrClientAll`: its `Err()`
returns client errors), with no resource for the options and no sort enumerations (the cache's
gets do not sort, `isEtcdKVE`). -/
theorem isEtcdKVE_of_km (api : Loc) (γ : KMNames) (dup : Bool) (pfx : GoString)
    (hpfx : pfx ≠ []) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv api γ.kv dup ∗
        kmInv γ ∗ ctxErrClientAll ⊢
      isEtcdKVE (EM := etcdModelOfKV γ) (kvIfaceOf api) pfx := by
  iintro ⟨#Pc, #Hkv, #Hinv, #Hall⟩
  unfold isEtcdKVE
  iintro !> %ctx %cs %key %sl %gs %lo %Φ !> ⟨#Hctx, #Hopts, #Hlo, %Hpre⟩ HΦ
  obtain ⟨Hnp, Ht, Hx, Hss, Hlin⟩ := Hpre
  ihave #Hsi : sortNamesIf (GF := GF) (opGetModel key gs).base.sortSet $$ []
  · rw [Hss]; unfold sortNamesIf; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  iunfold ctxErrClientAll at Hall
  ihave #Hce := Hall $$ %ctx %cs Hctx
  ihave #Hok := ctxOk_of_isContext ctx cs $$ Hctx
  ihave #Hor := optsAt_res sl gs iprop(True) $$ Hopts
  iapply (kv_get_km api γ dup pfx hpfx ctx cs key sl gs iprop(True) lo Hnp Ht Hx Hlin)
    $$ [] [HΦ]
  · iframe #
  inext
  iintro %resp %err ⟨-, #Hres, -, #Hse⟩
  iapply HΦ
  iframe Hres
  iapply errStrOk_of_statusErrOk $$ Hse

end proofs

end client
end EtcdGrove
end Perennial
