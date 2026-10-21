/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/cachekv/Main.lean` (2026-10-20). Lean-first
(no Rocq counterpart).

watchkv's `Main` (`Proof/.../watchkv/Main.lean`) with the watch through etcd's cache: `genAll`
picks the writers' Puts `trs` first; the server's start is putget's, at the workload of the Puts
picked (`watchkv.watchkv_alloc` at `trs.map pairOf`), with `NewServer`'s watchable-store readers
and one watch run slot, and the ghost step `watchkv.wk_served` (the KV specs and the watch server's
facts at the address, `srvNoDupKeys` from the workload). Then `clientv3.New` (one attempt per
call); the client's KV state in the client's invariant (`client.kvClientInv`, so that the cache's
gets have the ranges' updates, `client.kvRangeAu_of_inv`, and the writers' puts theirs, `put_au`);
the cache's client (`client.isEtcdClient_of_new_r`); `cache.New` (`New.spec` at the server's
model, the default configuration); a context (`WithCancel(Background())`); the cache's watch of
the prefix from revision `2` (`Cache.Watch.spec`, with one of `New`'s watch slots, its "open"
token, and the main thread's token, back from the server's start); the log `w` under its mutex
(`wsInv`), the writer goroutines (a wait group), the log's Puts `oks` taken under the lock,
`maxRev`, `collect` (the cache watch's log, `log_ck`), the cancel, and the check: `CheckOk` from
`collectOk` and the Puts' `okFact`s (`watchkv.revAt_agree`). Every start step's error ends `Main`
with `Failed`; `collect`'s `false` with `WatchEnded`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.genAll
public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.writer
public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.maxRev
public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.collect
public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.check
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Server
public import Spec.net.Listen
public import Spec.google_golang_org.grpc.Server__Serve
public import Spec.go_etcd_io.etcd.client.v3.New
public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Spec.context.ErrAny
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.watcher__RequestProgress
public import Spec.go_etcd_io.etcd.cache.v3.New
public import Spec.go_etcd_io.etcd.cache.v3.Cache__Watch
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.sync.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.context.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAlloc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.client.v3.CacheClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Served

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

omit package_sem in
/-- **The check's premise** (`CheckOk`), from what `collect` returns at `upTo` (`collectOk`) and
the successful Puts' facts (`okFact`), their revisions at most `upTo`: each Put's revision is a
watched event's (`collectOk`: the events reach `upTo`), whose key and value are the Put's
(`revAt_agree`). -/
theorem checkOk_of [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (E : apply.AEnv GF) (trs : List ckv) (upTo : w64) (evs : List cev) (oks : List crec)
    (hup : ∀ p ∈ oks, sint.Z p.rev' ≤ sint.Z upTo) :
    collectOk E (trs.map pairOf) upTo evs ∗ □ ([∗list] p ∈ oks, okFact E p) ⊢
      ⌜CheckOk evs trs oks⌝ := by
  unfold collectOk
  iintro ⟨⟨%Hc, #Hrevs⟩, #Hoks⟩
  obtain ⟨hup0, hlen, hevs⟩ := Hc
  ihave %H : ⌜∀ p, p ∈ oks → 2 ≤ sint.Z p.rev' ∧ ∃ e, evs[(sint.Z p.rev' - 2).toNat]? = some e ∧
      e.key' = p.key' ∧ e.val' = p.val'⌝ $$ []
  · iapply BI.pure_forall.2
    iintro %p
    by_cases hp : p ∈ oks
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
      ihave Hf := BigSepL.bigSepL_lookup (Φ := fun _ p => okFact (GF := GF) E p) hk $$ Hoks
      iunfold okFact at Hf
      icases Hf with ⟨%h2, #Hra⟩
      have hle := hup p hp
      have hlt : (sint.Z p.rev' - 2).toNat < evs.length := by
        rcases hup0 with h0 | h0
        · rw [h0] at hle; simp at hle; omega
        · omega
      obtain ⟨e, he⟩ : ∃ e, evs[(sint.Z p.rev' - 2).toNat]? = some e :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hidx : 2 + (sint.Z p.rev' - 2).toNat = (sint.Z p.rev').toNat := by omega
      ihave #He : watchkv.revAt E (sint.Z p.rev').toNat e.key' e.val' $$ []
      · rw [← hidx]; iapply Hrevs; ipureintro; exact he
      ihave %Hag := watchkv.revAt_agree E (sint.Z p.rev').toNat e.key' e.val' p.key' p.val' $$ [He Hra]
      · iframe #
      ipureintro; intro _; exact ⟨h2, e, he, Hag.1, Hag.2⟩
    · ipureintro; intro h; exact absurd h hp
  ipureintro
  exact ⟨hlen, hevs, H⟩

omit package_sem in
/-- `client.grpcCfgOk_of_started_w` with the logger's premise inside (so that `iapply` finds the
configuration from `srvServeFacts`; linkv's `grpcCfgOk_of_started'`). -/
theorem grpcCfgOk_of_started_w' [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (tos : List GoInterface) (K : Nat) :
    ⌜cfg.Logger' ≠ null⌝ ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvServeFacts s E cfg ∗
        srvWatchReaders s E K ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.eofVar ∗ v3rpc.runsNoRequireLeader ∗
        cfg.TracerOptions' ↦*□ tos ⊢
      ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk s C ∗
        ⌜C.A = v3rpc.srvKVAns s E ρ γr (W64 0) [] .none ∧ C.E = E⌝ ∗
        [∗list] _x ∈ List.replicate K (), mvcc.watchReader C.wsl E.s C.γ := by
  iintro ⟨%hlg, H⟩
  iapply (client.grpcCfgOk_of_started_w s E ρ γr cfg tos hlg K) $$ H

omit package_sem in
/-- The cache's default configuration is valid. -/
theorem cfgDefault_valid : CfgValid (cfgApply [] defaultConfigVal) := by
  unfold CfgValid cfgApply defaultConfigVal
  simp only [List.foldl_nil]
  constructor <;> decide

omit package_sem in
/-- The cache's default configuration is bounded. -/
theorem cfgDefault_bounded : CfgBounded (cfgApply [] defaultConfigVal) := by
  unfold CfgBounded cfgApply defaultConfigVal
  simp only [List.foldl_nil]
  refine ⟨by decide, by decide, by decide, by decide⟩

omit package_sem in
/-- The cache watch's options (`WithPrefix()`, `WithRev(2)`): the range of the prefix, from
revision `2`; `OpWatch` does not panic. -/
theorem ckWatch_opts :
    (opWatchModel ckPfx [withPrefixM, withRevM (W64 2)]).base.rangeEnd = prefixRangeEnd ckPfx ∧
      (opWatchModel ckPfx [withPrefixM, withRevM (W64 2)]).base.rev = W64 2 ∧
      ¬ opWatchPanics ckPfx [withPrefixM, withRevM (W64 2)] := by
  have h : ckPfx ≠ [] := by decide
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [opWatchModel, opWatchPanics, OpFull.watchPanics, opFold, OpFull.getInit, OpFull.newOp,
      OpModel.zero, withPrefixM, withRevM, h]

set_option maxHeartbeats 1600000 in
theorem Main.wp_proof
    (wp_genAll : genAll.spec (GF := GF) (hG := hG))
    (wp_writer : writer.spec (GF := GF) (hG := hG))
    (wp_maxRev : maxRev.spec (GF := GF) (hG := hG))
    (wp_collect : collect.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_FG : features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG))
    (wp_NewServer : ∀ [MemStorReg GF] [go_etcd_io.etcd.cache.v3.Assumptions],
      NewServer.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG))
    (wp_Server : v3rpc.Server.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Serve : grpc.Server.Serve.spec (GF := GF) (hG := hG))
    (wp_New : clientv3.New.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_RP : watcher.RequestProgress.spec (GF := GF) (hG := hG))
    (wp_CNew : ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EM : EtcdModel GF],
      EtcdGrove.New.spec (GF := GF) (hG := hG))
    (wp_CWatch : ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EM : EtcdModel GF],
      Cache.Watch.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS ESL ENG ESE CRE CEC N id bootLog nw nops Hbf Htb Hrb48 HrbN Hck Haf
    Hbuq Hnoc Hms hAs H0 H31 Hops Hmul
  have Htb31 : threadBound GF ≤ 2 ^ 31 := by omega
  wp_start as ⟨Haddr, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hboot, #Hzap, #Hsetlg, #Htd, #Hns, #Htk, #Hstop, #Hnrl⟩
  -- `io.EOF` (the server's and the watch client's) and `context`'s `closedchan`, from their
  -- packages' facts
  ihave #Heof : v3rpc.eofVar (GF := GF) $$ []
  · iapply v3rpc.eofVar_of_init
    iPkgInit
  ihave #Heo : client.eofOk (GF := GF) $$ []
  · iapply (client.eofOk_of_init hAs)
    iPkgInit
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  -- `tried := genAll(nw * nops)`: the Puts, picked before the member starts
  have hmul : sint.Z (nw * nops) = sint.Z nw * sint.Z nops := by
    have h1 : 0 ≤ sint.Z nw * sint.Z nops := Int.mul_nonneg H0 Hops
    word
  (try wp_auto)
  wp_apply (wp_genAll (nw * nops) (by rw [hmul]; exact Int.mul_nonneg H0 Hops))
    as %tsl ⟨%trs, Htrs, %Htrs⟩
  imod ownSlice_persist _ _ _ $$ Htrs with #Htrs
  have hpk : ∀ kv ∈ trs.map pairOf, ckPfx <+: kv.1 := by
    intro kv hkv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hkv
    have hk := (Htrs.2 p hp).1
    simp only [pairOf]
    simp only [genKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h | h <;> rw [h] <;> decide
  have hkeys : ∀ kv ∈ trs.map pairOf, keyPredForRange ckPfx (prefixRangeEnd ckPfx) kv.1 = true := by
    intro kv hkv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hkv
    have hk := (Htrs.2 p hp).1
    simp only [pairOf]
    simp only [genKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h | h <;> rw [h] <;> decide
  (try wp_auto)
  -- the imports' package facts
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pfeat : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pcache : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg %Hlg
  (try wp_auto)
  -- `peer`, the configuration's URLs and map
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %peer ⟨Hpeer, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  wp_auto
  wp_apply wp_map_make1 (K := GoString) (V := go_etcd_io.etcd.client.pkg.v3.types.URLs)
    as %pm Hpm
  wp_apply wp_mapInsert $$ Hpm as Hpm
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %curls ⟨Hcurls, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_FG as %fgp ⟨%Hfgp, #Hfg, #Hfgc⟩
  (try wp_auto)
  -- the storage registry (D19r (B)), `bootstrap`'s to join
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%γreg, Hreg⟩
  letI : MemStorReg GF := ⟨γreg⟩
  -- the configuration's URLs, read-only from here on (D19r (F))
  imod ownSlice_persist _ _ _ $$ Hpeer with #Hpeer
  imod ownSlice_persist _ _ _ $$ Hcurls with #Hcurls
  imod ownMap_persist _ _ _ $$ Hpm with #Hpm
  -- the ghost state `NewServer` takes (`putget_alloc`)
  imod (watchkv.watchkv_alloc (trs.map pairOf) id bootLog Hbf (by omega)) with ⟨%γ, %bud, %ρ, %E₀, %Φs, %Hal, Hghost,
    #Hcomm, #Hcinv, #Hbinv, #Hlb, #Hidc, #HNZ0, #Hpmint, #Hrdctx, Hids, HrdCred, Hwtok, Hidx, Hcok, Hrev,
    Hnk, #Hkvinv, Hetcd⟩
  obtain ⟨hcfg, hdyn, hcc, hboot, htr, hraft, hpol, hc0, hch, hlog, hcok, hwl, hpfx, hΦs⟩ := Hal
  -- (D21 M2) the raft network, the one member's slot
  imod (netNames_alloc (srvNet γ bud) ckDir (GMap.insert id () ∅)) with ⟨%γn, %Hγn, Hslots⟩
  ihave Hslot := (BigSepM.bigSepM_insert (GMap.lookup_empty id)).1 $$ Hslots
  icases Hslot with ⟨Hslot, -⟩
  have hblen : γ.reBoot.length ≤ 2 ^ 60 := by
    rw [hboot, Hbf.boot.1]; simp
  wp_apply (wp_NewServer _ ⟨[peerURL], [clientURL], GMap.insert go!"cachekv"
      (slice.mk peer (W64 (max (max (0 + 1) 0) 0)) (W64 (max (max (0 + 1) 0) 0))) ∅,
      fun _ => [peerURL]⟩ γ bud id bootLog ρ E₀ N Φs γn ckDir hraft hpol hc0 hch hlog hcok
      (by rw [hwl]; exact watchkv.workload_noGrant _) Hlg (by simp) rfl Htb31 Hrb48 HrbN
      -- (D21 M3) the run bound: `SnapshotCatchUpEntries` is `2 ^ 48` (`Main`'s)
      (by
        have h48 : uint.Z (W64 281474976710656 : w64) = 2 ^ 48 := by rfl
        have hne : (W64 281474976710656 : w64) ≠ W64 0 := by decide
        simp only [hne, ite_false, h48]
        omega)
      hblen
      hpfx hΦs ⟨fgp, Hfgp, rfl⟩)
    $$ [Hghost HrdCred Hids Hwtok Hidx Hcok Hrev Hnk Hreg Hslot] as %srv %err Hres
  · iframe
    iframe #
    isplitr
    · iapply Hboot
      ipureintro
      refine ⟨?_, ?_, hcfg, hdyn, hcc, hboot, htr⟩
      · unfold cfgOk; simp
      · exact ⟨rfl, rfl, ⟨_, rfl⟩, rfl⟩
    isplitr
    · iunfold bootCfgRO
      isplitr; · iExactEq Hpeer; rfl
      isplitr; · iExactEq Hcurls; rfl
      isplitr; · iExactEq Hpm; rfl
      iapply (BigSepM.bigSepM_insert (GMap.lookup_empty _)).2
      isplitr
      · iExactEq Hpeer; rfl
      iapply BigSepM.bigSepM_empty.2; itrivial
    isplitl [Hreg]
    · iunfold memStorRegAuth; iexact Hreg
    isplitr; · ipureintro; exact Hγn
    isplitr; · ipureintro; exact Hck
    isplitr; · ipureintro; exact Haf
    isplitr; · ipureintro; exact Hbuq
    isplitr; · ipureintro; exact Hnoc
    iapply Htk
    ipureintro; rfl
  icases Hres with (⟨%Hsn, %Herr⟩ | ⟨%Herr, %γA, %ci, %TM, %E, %γn, %b, %HE, #Hwb, Hbuilt, Hgap,
    Hserve, Hsv, Hmon, -, HWR⟩)
  · -- `NewServer` failed: `Main` returns
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Herr
  wp_auto
  -- `s.Start()`
  ihave Hsb := isServerBuilt_of_gap srv γA ci TM E ρ ρ.rd _ γn b (W64 0) (W64 0) (W64 0) bootKV N
    $$ [Hbuilt Hgap]
  · iframe
  iunfold srvServeBuilt at Hserve
  icases Hserve with ⟨#Hsf, Hwpi, Hbemu, Hlts, Hlgs, Hrds, Hsts⟩
  icases replicate_take2 _ _ (by omega) $$ Hlgs with ⟨Hlg1, Hlg2, Hlgs⟩
  iunfold srvMonitorCfg at Hmon
  icases Hmon with ⟨#Hmc, #Hmd, #Hmf, Hlgm⟩
  ihave #Hoff : srvMonitorsOff srv $$ []
  · iunfold srvMonitorsOff
    isplitr; · iExactEq Hmc; rfl
    isplitr; · iExactEq Hmd; rfl
    iexists _
    iframe Hmf Hfgc
  wp_apply (wp_Start srv γA ci TM E ρ ρ.rd _ γn b (W64 0) (W64 0) (W64 0) bootKV N HrbN rfl)
    $$ [Hsb Htok Hlg1 Hlg2 Hsv Hlgm] as ⟨%γw, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, -, -⟩
  · iframe; iframe #
  (try wp_auto)
  -- `v3rpc.Server(s, nil, nil)`: its configuration from `NewServer`'s and `Start`'s
  ihave ⟨%C, #Hgc, %HC, HWRs⟩ : ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk srv C ∗
      ⌜C.A = v3rpc.srvKVAns srv E { ρ with wait := γw } ρ.rd (W64 0) [] .none ∧ C.E = E⌝ ∗
      [∗list] _x ∈ List.replicate 64 (), mvcc.watchReader C.wsl E.s C.γ $$ [HWR]
  · iapply (grpcCfgOk_of_started_w' srv E { ρ with wait := γw } ρ.rd _ [] 64)
    iframe; iframe #
    isplitr
    · ipureintro; exact Hlg
    iapply ownSlice_nil
  wp_apply (wp_Server Hms srv C _ slice.nil [] Hbuq) $$ [Hlg3 Hbemu Hgo Hwpi]
    as %gs ⟨%q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %cid, %mid, %R, %d',
      Hgsn, %Hregs, #Hq, #Hkvs, #Hws, %HR, #Hil, #Him, #Hiu, #Hims, #His, Hlg4, Hbemu2, Hgo2,
      Hwpi2⟩
  · iframe; iframe #
    isplitr
    · ipureintro; simp
    isplitr
    · iapply ownSlice_nil
    ipureintro; intro v hv; cases hv
  -- the watch server's environment is the server's: `E` is `R.E` from here on
  obtain ⟨hRs, hRE, hRw, hRγ⟩ := HR
  rw [HC.2] at hRE
  subst hRE
  -- `net.Listen("tcp", clientAddr)`
  wp_apply (wp_Listen go!"tcp" go!"127.0.0.1:23851") $$ [Haddr] as %lis %lerr Hlis
  · iframe; ipureintro; rfl
  icases Hlis with (⟨%Hlerr, Hlis⟩ | %Hlerr)
  rotate_left
  · cases lerr with
    | nil => exact absurd rfl Hlerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Hlerr
  wp_auto
  -- the ghost step between `Listen` and `go gs.Serve(l)`: etcd's KV specs at the address
  haveI := Hms
  icases replicate_take2 _ _ (by omega) $$ Hlts with ⟨-, -, Hlts⟩
  icases replicate_take2 _ _ (by omega) $$ Hrds with ⟨Hrd1, -, Hrds⟩
  ihave Hslots := client.etcdGrpcSlots_of_started srv R.E ρ.rd 1 (64 - 2) 64
      (Int.toNat sync.rwmutex.actualMaxReaders) (by omega) (by omega)
      (by have := sync.actualMaxReaders_ge_2; omega) $$ [Hlts Hlgs Hrds Hsts Hrslots]
  · iframe
  -- (D23) one watch run slot: two of the watchable store's readers, one of the request path's
  ihave Hwslots := client.watchRunSlots_of R 1 64 1 (by omega) (by omega) $$ [HWRs Hrd1]
  · rw [hRw, hRγ]
    iframe HWRs
    isplitl [Hrd1]
    · simp only [List.replicate]
      iapply BigSepL.bigSepL_cons.2
      iframe Hrd1
      iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro
    rw [sync.rwmutex.actualMaxReaders_unseal]
    omega
  -- (D23) the watch server's facts: `srvNoDupKeys` from the workload, the transport premise,
  -- `io.EOF`
  ihave %Hst := client.watchSrvLink_of_server pw R $$ Hws
  ihave #Hinvs := client.srvKVInvs_of_read srv R.E ρ.rd $$ Hrd
  ihave #H00 := watchkv.cert0_of_server pw R $$ Hws
  ihave #Hnd := watchkv.srvNoDupKeys_wk R ρ.rd (trs.map pairOf) hwl hlog Hst $$ [Hinvs H00]
  · iframe #
  ihave #Hkva := client.kvServerAt_of_is p srv C.A cid mid C.n $$ Hkvs
  rw [HC.1]
  imod (watchkv.wk_served ⟨R, go!"127.0.0.1:23851", [], null, null, ckPfx, null⟩ go!"127.0.0.1:23851"
      gs q p pw srv lis R.E { ρ with wait := γw } ρ.rd cid mid C.n il im iu ims is svcs regs sregs
      1 1 Hregs.1 rfl rfl (by simp) Hms.watch_impl Hregs.2)
    $$ [Hgsn Hlis Hslots Hwslots] with ⟨Hserv, #HPut, #HRange, #HWF⟩
  · iframe; iframe #
    iintro !>
    imodintro
    iunfold idCred
    ipureintro; exact Hrb48
  -- `go gs.Serve(l)`
  wp_apply wp_fork $$ [Hserv]
  · wp_apply (wp_Serve gs lis) $$ [$Hserv] as %serr -
    ipureintro; exact isPanic_intoVal serr
  -- `clientv3.New(Config{Endpoints: {clientAddr}, Logger: lg})`
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %eps ⟨Heps, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  wp_apply (wp_New _ go!"127.0.0.1:23851"
      ⟨R, go!"127.0.0.1:23851", [], null, null, ckPfx, null⟩) $$ [] as %cl %cerr Hcl
  · iframe #
    iunfold clientCfgOk
    simp only
    iframe #
    isplitr
    · isplitr
      · iapply ownSlice_nil
      ipureintro
      refine ⟨?_, ?_⟩
      · unfold plainEndpoint; decide
      · simp [Hlg]
    ipureintro; exact Htb31
  icases Hcl with (⟨%Hcerr, #Hnc, Hone⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Hcerr
  wp_auto
  ihave #Hone := Hone $$ []
  · ipureintro; trivial
  -- the client's KV state in the client's invariant (its revision a monotone counter), which the
  -- cache's gets (`kvRangeAu`) and the writers' puts (`put_au`) open
  imod client.kvClientInv_alloc ρ.rd _ ⊤ $$ Hetcd with ⟨%γm, #Hkci⟩
  ihave #Hra := client.kvRangeAu_of_inv R.E ρ.rd γm $$ [Hinvs Hkci]
  · iframe #
  -- the cache's client (`isEtcdClient`): `clientv3.New`'s, with the watch server's facts (D19f)
  ihave #Hecl := client.isEtcdClient_of_new_r wp_ErrAny hAs wp_Watch wp_RP cl
    go!"127.0.0.1:23851" ⟨R, go!"127.0.0.1:23851", [], null, null, ckPfx, null⟩ srv R.E ρ.rd cid
    mid rfl rfl (show prefixRangeEnd ckPfx ≠ [W8 0] by decide)
    $$ []
  · iframe #
  (try wp_auto)
  -- `c, err := cache.New(cli, prefix)`: the default configuration
  ihave #Hcopts : cfgOptsAt (GF := GF) slice.nil [] $$ []
  · iunfold cfgOptsAt
    iexists ([] : List GoFunc)
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    simp at Hf
  wp_apply (wp_CNew (EM := v3rpc.etcdModelOfServer R.E) cl ckPfx slice.nil []) $$ []
    as %c %cerr Hnew
  · iframe #
    isplitr
    · ipureintro; intro _; exact cfgDefault_bounded
    ipureintro; unfold cacheWgOwedMax; omega
  irevert Hnew
  unfold newCacheResult
  rw [if_pos cfgDefault_valid]
  iintro Hnew
  icases Hnew with ⟨%Hcerr, %cf, %γrd, %γd, %γnn, #Hcf, %Hcfe, Hhandles⟩
  subst Hcerr
  (try wp_auto)
  iunfold cacheHandles at Hhandles
  icases Hhandles with ⟨-, Hslots, -, -, Hopen⟩
  ihave ⟨Hslot, -⟩ : cacheWatchSlot (EM := v3rpc.etcdModelOfServer R.E) cf γd
      (sint.nat (cfgApply [] defaultConfigVal).HistoryWindowSize') ∗ True $$ [Hslots]
  · have hmr : maxReaders - 2 = (maxReaders - 3) + 1 := by
      have := sync.actualMaxReaders_ge_2
      unfold maxReaders
      rw [sync.rwmutex.actualMaxReaders_unseal] at *
      omega
    rw [hmr]
    simp only [List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hslots with ⟨Hs, -⟩
    iframe Hs
  -- the main thread's token, back from the server's start (`srvGoRes`)
  iunfold srvGoRes at Hgo2
  icases Hgo2 with ⟨-, Htok⟩
  -- `wctx, cancel := context.WithCancel(context.Background())`
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Pctx $Hcci]
    as %wctx %γc %cancel ⟨#Hcancel, #Hwctx, -⟩
  (try wp_auto)
  -- the watch's options: a prefix watch from revision `2`
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_WithRev (W64 2) as %f2 #Hf2
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  ipersist Hosl
  (try wp_auto)
  generalize hosl : slice.mk osl _ _ = optsSl
  have hfs : ([f1, zero_val GoFunc].set (sint.nat (W64 (0 + 1))) f2) = [f1, f2] := rfl
  ihave #Hopts : optsAt optsSl ([withPrefixM, withRevM (W64 2)] : List (OpFull → OpFull)) $$ []
  · iunfold optsAt
    iexists _
    iframe Hosl
    isplitr
    · ipureintro; rw [hfs]; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rw [hfs] at Hf
    rcases i with _ | _ | i
    · cases Hf; cases Hg; iexact Hf1
    · cases Hf; cases Hg; iexact Hf2
    · simp at Hf
  -- `wch := c.Watch(wctx, prefix, ...)`: the cache's watch contract, from revision `2`
  wp_apply (wp_CWatch (EM := v3rpc.etcdModelOfServer R.E) c cf γrd γd _ wctx
      ({ Values := ∅, Deadline := none, Done_gn := γc, PDone := iprop(True) } :
        context.ContextDesc (IProp GF)) ckPfx optsSl
      ([withPrefixM, withRevM (W64 2)] : List (OpFull → OpFull)) 1)
    $$ [Hslot Hopen Htok] as %wch ⟨Hopen, Htok, %γw, #Hwch, Hcons⟩
  · iframe; iframe #
    ipureintro; exact ckWatch_opts.2.2
  have hre : (withPrefixM (OpFull.getInit ckPfx)).base.rangeEnd = prefixRangeEnd ckPfx := by
    have h : ckPfx ≠ [] := by decide
    simp [withPrefixM, OpFull.getInit, OpFull.newOp, h]
  rw [hre, Hcfe.1]
  (try wp_auto)
  icases typedPointsto_split _ _ _ $$ «$r0» with Hr0
  try simp only [TypedPointsto.typedPointstoDef]
  icases Hr0 with ⟨mu, ok, -⟩
  imod sync.init_Mutex (wsInv «$r0_ptr» R.E) ⊤
      (structFieldRef github_com.mit_pdos.etcd_grove.examples.cachekv.writes go!"mu" «$r0_ptr»)
    $$ mu [ok] with #Hmu
  · inext
    iunfold wsInv
    iexists slice.nil, []
    iframe ok
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    iintro !>
    iapply BigSepL.bigSepL_nil.2; itrivial
  ipersist w
  ipersist cli
  ipersist tried
  ipersist nops
  -- the writers' wait group
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, Hwg⟩
  imod sync.join.init wg_ptr γwg $$ Hwg with Hwg
  ihave IH : (∃ (k : w64) (na : w32),
      "i" ∷ i_ptr ↦ k ∗ "Hwg" ∷ sync.join.ownAdder wg_ptr na iprop(True) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z nw ∧ sint.Z na = sint.Z k⌝ : IProp GF)
    $$ [i Hwg]
  · iexists W64 0, W32 0
    iframe
    ipureintro
    exact ⟨by decide, H0, by decide⟩
  wp_for IH
  wp_if_destruct
  · -- a writer: `lo := i * nops`, `wg.Add(1)`, `go func() { writer(...); wg.Done() }()`
    have Hlt : sint.Z k < sint.Z nw := by simpa using Hif
    have hlo : sint.Z (k * nops) = sint.Z k * sint.Z nops := by
      have h1 : 0 ≤ sint.Z k * sint.Z nops := Int.mul_nonneg Hk.1 Hops
      have h2 : sint.Z k * sint.Z nops ≤ sint.Z nw * sint.Z nops :=
        Int.mul_le_mul_of_nonneg_right (by omega) Hops
      word
    have hhi : sint.Z (k * nops + nops) = sint.Z k * sint.Z nops + sint.Z nops := by
      have h2 : (sint.Z k + 1) * sint.Z nops ≤ sint.Z nw * sint.Z nops :=
        Int.mul_le_mul_of_nonneg_right (by omega) Hops
      have h1 : 0 ≤ sint.Z k * sint.Z nops := Int.mul_nonneg Hk.1 Hops
      rw [Int.add_mul, Int.one_mul] at h2
      word
    (try wp_auto)
    wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add iprop(True) wg_ptr iprop(True) na) $$ [Hwg]
      as ⟨Hwg, Hdone⟩
    · iframe; ipureintro; word
    ipersist lo
    wp_apply wp_fork $$ [Hdone]
    · (try wp_auto)
      wp_apply (wp_writer cl go!"127.0.0.1:23851" ⟨R, go!"127.0.0.1:23851", [], null, null, ckPfx, null⟩
          R.E ρ.rd cid mid «$r0_ptr» tsl trs (k * nops) (k * nops + nops) (trs.map pairOf) γm hAs hwl
          rfl (by rw [hlo]; exact Int.mul_nonneg Hk.1 Hops) (by rw [hlo, hhi]; omega)
          (by
            rw [hhi, Htrs.1]
            have h2 : (sint.Z k + 1) * sint.Z nops ≤ sint.Z nw * sint.Z nops :=
              Int.mul_le_mul_of_nonneg_right (by omega) Hops
            rw [Int.add_mul, Int.one_mul] at h2
            have h0 : (0 : Int) ≤ sint.Z (nw * nops) := by
              rw [hmul]; exact Int.mul_nonneg H0 Hops
            have e : ((sint.nat (nw * nops) : Nat) : Int) = sint.Z (nw * nops) := by word
            rw [e, hmul]
            omega)) $$ []
      · iframe #
      (try wp_auto)
      wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr) $$ [Hdone]
      · iframe
      itrivial
    wp_for_post
    iframe
    iexists (k + W64 1), (na + W32 1)
    iframe
    isplitl [Hwg]
    · iapply sync.join.ownAdder_wand $$ [] Hwg
      iintro -; itrivial
    ipureintro
    refine ⟨by word, by word, by word⟩
  -- the writers are done: `wg.Wait()`
  wp_apply (sync.join.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait _ na wg_ptr) $$ [$Hwg] as -
  (try wp_auto)
  -- the successful Puts, taken out of the log under the lock
  wp_apply (sync.Mutex.wp_Lock (structFieldRef github_com.mit_pdos.etcd_grove.examples.cachekv.writes
      go!"mu" «$r0_ptr») (wsInv «$r0_ptr» R.E)) $$ [] as ⟨Hown, Hws0⟩
  · iframe #
  iunfold wsInv at Hws0
  icases Hws0 with ⟨%osl, %oks, Hok, Hos, Hocap, #Hoks⟩
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Unlock (structFieldRef github_com.mit_pdos.etcd_grove.examples.cachekv.writes
      go!"mu" «$r0_ptr») (wsInv «$r0_ptr» R.E)) $$ [Hown Hok]
  · iframe #
    iframe Hown
    inext
    iunfold wsInv
    iexists slice.nil, []
    iframe Hok
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    iintro !>
    iapply BigSepL.bigSepL_nil.2; itrivial
  (try wp_auto)
  -- `collect(wch, maxRev(oks))`, then `cancel()`
  wp_apply (wp_maxRev osl oks (DFrac.own 1)) $$ [Hos] as %m ⟨Hos, %Hm⟩
  · iframe
  wp_apply (wp_collect R.E ρ.rd (trs.map pairOf) wch γw (prefixRangeEnd ckPfx) m hwl hlog hpk
      hkeys) $$ [Hcons]
    as %esl %ok Hcol
  · iframe; iframe #
  (try wp_auto)
  wp_apply Hcancel $$ [] as -
  · itrivial
  (try wp_auto)
  cases ok
  · -- the watch ended before it reported every successful Put
    (try wp_auto)
    iapply HΦ; ipureintro; right; right; rfl
  ihave ⟨%evs, Hes, Hcok⟩ := Hcol $$ %rfl
  ihave %HCk := checkOk_of R.E trs m evs oks Hm.2 $$ [Hcok]
  · iframe Hcok
    iexact Hoks
  imod ownSlice_persist _ _ _ $$ Hes with #Hes
  imod ownSlice_persist _ _ _ $$ Hos with #Hos
  (try wp_auto)
  wp_apply (wp_check esl tsl osl evs trs oks HCk) $$ []
  · iframe #
  (try wp_auto)
  iapply HΦ; ipureintro; left; rfl

end proof

end cachekv
end EtcdGrove
end Perennial
