/- Lean-first (no Rocq counterpart).

# The cache workload across machines: its vocabulary (#50 F6, `notes/etcd-dist-plan.md` §29)

`RunCache` (`examples/etcd/dist/client/watch.go`) is the single-process cache example (`etcd_cache.Main`,
`Proof/.../cache/Main.lean`) with its cache on the orchestrator and its writers on client machines of their
own (the watch workload's writers, `remoteWriters`, N10a). The argument is the single-process one, over the
cluster's KV `Γ.kv` (the watch workload's adapter, `WatchWorkDefs.lean`) instead of the member's server facts:

* **The cache's client** (`isEtcdClient_of_dist`): `clientv3.New`'s client of the endpoints meets the cache's
  client contract (`isEtcdClient`) at the adapter's model `etcdModelOfKV γ` (`γ.kv = Γ.kv`), as
  `client.isEtcdClient_of_km` in one process:
  - its watches by `Watch_dist` (`kvWatcherW_of_dist`, `isEtcdWatcher_of_kmW`: N10a's);
  - its progress requests by `RequestProgress_dist` (`isEtcdProgressNotifier_of_dist`);
  - its gets by `kv.Get.spec` at the client's `isKv` of the auth-off view (`isKv_of_kvClientAt`;
    `kv_get_km_dist`, `isEtcdKVE_of_dist`): `client.kv_get_km`'s proof over it, at any context
    (`ctxErrClientAllW_of`). The cache needs the error arm's `statusErrOk err`: its watch loop prints `get`'s
    error with `fmt.Printf`'s `%v` (`getWatchLoop`, `isEtcdKVE`'s `errStrOk`); `kv.Get.spec`'s `kvErr` gives it.
* `wkW_eq`: the writers' plan property (`etcd_partition.wkW`, the writer wire's `kmOf`) is the cache example's
  (`etcd_watch.wkW`, which its helpers' specs name): the same definition, copied.
* `cacheShare addrs ns`: the orchestrator's share, the watch workload's (`watchShare writersShare`): the cache
  workload is its deployment's sole writer too, and its writers are the watch workload's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WatchWorkDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterWire
public import Spec.go_etcd_io.etcd.client.v3.kv__Get
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Proof.go_etcd_io.etcd.client.v3.ServerKVGetDefs
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas
public import Proof.go_etcd_io.etcd.client.v3.EtcdModelKV
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk
public import Proof.go_etcd_io.etcd.cache.v3.InvNew
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WatchWorkload
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CacheGetFacts

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3
  go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcdstart
open github_com.mit_pdos.etcd_grove.examples.lib.remote

/-- **The writers' plan property is the cache example's** (`etcd_partition.wkW` and `etcd_watch.wkW`: the
same definition, copied). -/
theorem wkW_eq (P : List (GoString × GoString)) : etcd_partition.wkW P = etcd_watch.wkW P := by
  funext ch
  unfold etcd_partition.wkW etcd_watch.wkW etcd_partition.WkLog etcd_watch.WkLog
    etcd_partition.wkRev etcd_watch.wkRev
  rfl

section pure
variable [GooseExts]

/-- The keys `RunCache`'s `GenAll` picks from (`ck/k0`, `ck/k1`, `ck/k2`: the cache example's). -/
abbrev ckKeys : List GoString := [go!"ck/k0", go!"ck/k1", go!"ck/k2"]

/-- A Put `GenAll` picks from `ckKeys` is small (`wkvSmall`, the writers' wire's bound). -/
theorem ck_genKv_small (p : wkv) (h : GenKv ckKeys p) : wkvSmall p := by
  obtain ⟨hk, hv⟩ := h
  simp only [ckKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  simp only [genVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  refine ⟨?_, ?_⟩
  · rcases hk with h | h | h <;> rw [h] <;> decide
  · rcases hv with h | h | h | h <;> rw [h] <;> decide

/-- The Puts' keys are under the prefix `ck/`. -/
theorem ck_genKeys_pfx (trs : List wkv) (h : ∀ p ∈ trs, GenKv ckKeys p) :
    ∀ kv ∈ trs.map pairOf, etcd_cache.ckPfx <+: kv.1 := by
  intro kv hkv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hkv
  have hk := (h p hp).1
  simp only [pairOf]
  simp only [ckKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with h | h | h <;> rw [h] <;> decide

/-- The Puts' keys are in the prefix's range. -/
theorem ck_genKeys_range (trs : List wkv) (h : ∀ p ∈ trs, GenKv ckKeys p) :
    ∀ kv ∈ trs.map pairOf,
      keyPredForRange etcd_cache.ckPfx (prefixRangeEnd etcd_cache.ckPfx) kv.1 = true := by
  intro kv hkv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hkv
  have hk := (h p hp).1
  simp only [pairOf]
  simp only [ckKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with h | h | h <;> rw [h] <;> decide

/-- The cache's default configuration is valid (the cache example's `cfgDefault_valid`, copied: that
file is a proof module). -/
theorem ck_cfgDefault_valid : CfgValid (cfgApply [] defaultConfigVal) := by
  unfold CfgValid cfgApply defaultConfigVal
  simp only [List.foldl_nil]
  constructor <;> decide

/-- The cache's default configuration is bounded (`cfgDefault_bounded`, copied). -/
theorem ck_cfgDefault_bounded : CfgBounded (cfgApply [] defaultConfigVal) := by
  unfold CfgBounded cfgApply defaultConfigVal
  simp only [List.foldl_nil]
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The cache's `Get` options (`WithPrefix()`, `WithRev(m)`): the range of the prefix, at revision
`m`; `OpGet` does not panic (`ckGet_opts`, copied). -/
theorem ck_get_opts (m : w64) :
    (opGetModel etcd_cache.ckPfx [withPrefixM, withRevM m]).base.rangeEnd =
        prefixRangeEnd etcd_cache.ckPfx ∧
      (opGetModel etcd_cache.ckPfx [withPrefixM, withRevM m]).base.rev = m ∧
      ¬ opGetPanics [withPrefixM, withRevM m] := by
  have h : etcd_cache.ckPfx ≠ [] := by decide
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [opGetModel, opGetPanics, op_simps, h]

/-- The cache watch's options (`WithPrefix()`, `WithRev(2)`): the range of the prefix, from
revision `2`; `OpWatch` does not panic (`ckWatch_opts`, copied). -/
theorem ck_watch_opts :
    (opWatchModel etcd_cache.ckPfx [withPrefixM, withRevM (W64 2)]).base.rangeEnd =
        prefixRangeEnd etcd_cache.ckPfx ∧
      (opWatchModel etcd_cache.ckPfx [withPrefixM, withRevM (W64 2)]).base.rev = W64 2 ∧
      ¬ opWatchPanics etcd_cache.ckPfx [withPrefixM, withRevM (W64 2)] := by
  have h : etcd_cache.ckPfx ≠ [] := by decide
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [opWatchModel, opWatchPanics, OpFull.watchPanics, op_simps, h]

end pure

section client
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A KV client of the view's linearizable exact get at the adapter's model** (`client.kv_get_km` over
`kv.Get.spec`; see the file header). -/
theorem kv_get_km_dist (wp_Get : kv.Get.spec (GF := GF) (hG := hG)) [π : NetProtoGS]
    (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView) (hauth : Γ.auth = false)
    (γ : KMNames) (hγ : γ.kv = Γ.kv)
    (pfx : GoString) (hpfx : pfx ≠ [])
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) (lo : w64)
    (Hnp : ¬ opGetPanics gs) (Ht : (opGetModel key gs).t = W64 1)
    (Hx : (opGetModel key gs).getExact)
    (Hlin : (opGetModel key gs).base.serializable = false) (Hsz : opSizeOk (opGetModel key gs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        kvClientAt cl api eps V Γ ∗
        kmInv γ ∗ sortNamesIf (opGetModel key gs).base.sortSet ∗ ctxOk ci cd ∗
        ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗ etcdReached (EM := etcdModelOfKV γ) lo }}
      (App (App (App (Val #(methods (kvIfaceOf api).ty go!"Get" (kvIfaceOf api).v))
        (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (
        R ∗ kvGetResultC (EM := etcdModelOfKV γ) pfx lo (opGetModel key gs) resp err ∗
        statusErrOk err) }} := by
  iintro %Φ ⟨#Pc, Hlt, #Hkv, #Hinv, #Hsi, #Hctx, #Hce, #Hopts, HR, #Hlo⟩ HΦ
  have hws : (rangeWireOf (opGetModel key gs)).base.serializable = false := by
    rw [(wire_fields _).2.2.2.2.2.2.1]; exact Hlin
  -- the floor: changes the client saw, `lo` of them or more, and the read update after them
  imod km_reached_lb γ lo $$ Hlo with ⟨%l0, #Hl0, %Hll⟩
  ihave #Hau := km_read_au γ l0 $$ [$Hinv $Hl0]
  ihave #Hik := isKv_of_kvClientAt cl api eps V Γ hauth $$ Hkv
  iapply (wp_Get api Γ.kv false ci cd key sl gs R (kmSeenQ γ l0)) $$ [Hlt HR]
  · iframe #
    iframe Hlt
    iframe
    isplitl []
    · ipureintro; exact ⟨Hnp, Ht⟩
    isplitl []; rotate_left
    · ipureintro; exact Hsz
    imodintro
    iright
    isplitl []
    · ipureintro; exact hws
    iunfold kvReadAu at Hau
    iunfold kvAu at Hau
    rw [← hγ]
    iexact Hau
  inext
  iintro %resp %err ⟨Hlt, HR, Hout⟩
  iapply HΦ
  iframe Hlt
  iframe HR
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hs⟩ | ⟨%Herr, #Hke⟩)
  rotate_left
  · iunfold kvErr at Hke
    icases Hke with ⟨-, #Hse, -⟩
    isplitl
    · unfold kvGetResultC; ileft; ipureintro; exact Herr.1
    iexact Hse
  simp only [hws, Bool.false_eq_true, ↓reduceIte]
  iunfold kmSeenQ at HQ
  icases HQ with ⟨#Hlb, %Hpre⟩
  obtain ⟨hrle, hsrv, -, hrev, h3, hok⟩ := Hs
  replace h3 := h3.lt
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
        iapply kvValAt_of_kvIs; iexact Hkw
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
  rw [Herr]
  iapply statusErrOk_nil

/-- **A KV client of the view meets the cache's get contract** (`isEtcdKVE`) at the adapter's model
(`client.isEtcdKVE_of_km` over `kv_get_km_dist`): any context (`ctxErrClientAllW`), no resource for the
options, no sort enumerations. -/
theorem isEtcdKVE_of_dist (wp_Get : kv.Get.spec (GF := GF) (hG := hG)) [π : NetProtoGS]
    (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView) (hauth : Γ.auth = false)
    (γ : KMNames) (hγ : γ.kv = Γ.kv)
    (pfx : GoString) (hpfx : pfx ≠ []) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvClientAt cl api eps V Γ ∗
        kmInv γ ∗ ctxErrClientAllW ⊢
      isEtcdKVE (EM := etcdModelOfKV γ) (kvIfaceOf api) pfx := by
  iintro ⟨#Pc, #Hkv, #Hinv, #Hall⟩
  unfold isEtcdKVE
  iintro !> %ctx %cs %key %sl %gs %lo %Φ !> ⟨Hlt, #Hctx, #HctxO, #Hopts, #Hlo, %Hpre⟩ HΦ
  obtain ⟨Hnp, Ht, Hx, Hss, Hlin, Hsz⟩ := Hpre
  ihave #Hsi : sortNamesIf (GF := GF) (opGetModel key gs).base.sortSet $$ []
  · rw [Hss]; unfold sortNamesIf; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  iunfold ctxErrClientAllW at Hall
  ihave #Hce := Hall $$ %ctx %cs Hctx
  ihave #Hok := ctxOk_of_isContext ctx cs $$ [$Hctx $HctxO]
  ihave #Hor := optsAt_res sl gs iprop(True) $$ Hopts
  iapply (kv_get_km_dist wp_Get cl api eps V Γ hauth γ hγ pfx hpfx ctx cs key sl gs iprop(True) lo Hnp Ht Hx
      Hlin Hsz) $$ [Hlt] [HΦ]
  · (try iframe Hlt)
    iframe #
  inext
  iintro %resp %err ⟨Hlt, -, #Hres, #Hse⟩
  iapply HΦ
  iframe Hlt
  iframe Hres
  iapply errStrOk_of_statusErrOk $$ Hse

/-- **A watch client of the view is the cache's progress notifier** (`client.isEtcdProgressNotifier_of_watcher`
over the interim `RequestProgress_dist`, a hypothesis). -/
theorem isEtcdProgressNotifier_of_dist (wp_RP : RequestProgress_dist.spec (GF := GF) (hG := hG))
    [π : NetProtoGS] (cl w : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ watchClientAt cl w eps V Γ ⊢
    isEtcdProgressNotifier (watcherIfaceOf w) := by
  iintro ⟨#P1, #P2, #P3, #Hw⟩
  unfold isEtcdProgressNotifier
  iintro !> %ctx %cs %Φ !> ⟨#Hctx, #HctxO⟩ HΦ
  iapply (wp_RP cl w eps V Γ ctx cs) $$ [] [HΦ]
  · iframe #
  inext
  iintro %err #Hse
  iapply HΦ
  ihave #Hs := errStrOk_of_statusErrOk err $$ Hse
  iunfold errStrOk at Hs
  iexact Hs

/-- **`New`'s client of endpoints serving the view is the cache's client** at the adapter's model (see the
file header; `client.isEtcdClient_of_km` across machines): its `KV` a KV client of the view
(`kv.Get.spec`, auth off), its `Watcher` a watch client of it (`Watch_dist`, `RequestProgress_dist`), for a
non-empty prefix. -/
theorem isEtcdClient_of_dist (wp_Get : kv.Get.spec (GF := GF) (hG := hG))
    (wp_Watch : Watch_dist.spec (GF := GF) (hG := hG))
    (wp_RP : RequestProgress_dist.spec (GF := GF) (hG := hG)) [π : NetProtoGS]
    (cl api w : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView) (hauth : Γ.auth = false)
    (γ : KMNames) (hγ : γ.kv = Γ.kv)
    (pfx : GoString) (hp : pfx ≠ []) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ ctxErrClientAllW ∗
      kvClientAt cl api eps V Γ ∗ watchClientAt cl w eps V Γ ∗ kmInv γ ⊢
    isEtcdClient (EM := etcdModelOfKV γ) cl pfx := by
  iintro ⟨#P1, #P2, #P3, #Hall, #Hkv, #Hwc, #Hinv⟩
  ihave #Hkw0 := kvWatcherW_of_dist wp_Watch cl w eps V Γ $$ [P1 P2 P3 Hwc]
  · iframe #
  ihave #Hkw : kvWatcherW (GF := GF) w γ.kv $$ []
  · rw [hγ]; iexact Hkw0
  ihave #Hkv' := Hkv
  iunfold kvClientAt at Hkv'
  icases Hkv' with ⟨-, -, #HKV, -⟩
  ihave #Hwc' := Hwc
  iunfold watchClientAt at Hwc'
  icases Hwc' with ⟨-, -, #HW, -⟩
  unfold isEtcdClient
  iexists kvIfaceOf api, watcherIfaceOf w
  iframe HKV HW
  isplitr
  · iapply isEtcdKVE_of_dist wp_Get cl api eps V Γ hauth γ hγ pfx hp
    iframe #
  isplitr
  · iapply isEtcdWatcher_of_kmW w γ pfx hp
    iframe #
  iapply isEtcdProgressNotifier_of_dist wp_RP cl w eps V Γ
  iframe #

end client

/-! ## The orchestrator's share (global) -/

section shares
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS] [ρ : RemoteGS]

/-- **The cache workload's orchestrator share** at the endpoints `addrs` and the writer machines `ns`: the
watch workload's (`watchShare` at the writers' share `writersShare`; see the file header). -/
abbrev cacheShare (addrs ns : List GoString) : IProp GF :=
  watchShare (Gg := Gg) (writersShare (Gg := Gg)) addrs ns

end shares

end etcd_dist_client
end EtcdGrove
end Perennial
