/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/cache/Main.lean` (2026-10-20). Lean-first
(no Rocq counterpart).

watchkv's `Main` (`Proof/.../watchkv/Main.lean`, before 2026-10-26, when watchkv stopped using the
adapter) with the watch through etcd's cache: `genAll`
picks the writers' Puts `trs` first; the server's start is watchkv's, the examples' shared one
(`etcdstart.alloc1`; D48: the adapter's invariant over the KV state's half, `client.kmInv_alloc` at
the plan's fact `etcd_watch.wkW (trs.map pairOf)`; `etcdstart.StartPeriodicServer` (since 2026-11-02;
the store's fact for watches from the plan, `noDupKeys_of_wk`), `etcdstart.Serve` with one
watch run slot, `etcd_noRefusal` and `etcd_watch.wk_served_nd` as the ghost step, D33). Then
`etcdstart.NewClient` (etcd's default configuration; the member refusal-free, so `clientWriteOnce`,
D29); the cache's client at the adapter's model (`client.isEtcdClient_of_km`: its `KV` a client of
the KV, `client.isKv_of_regs`, its `Watcher` a watcher of the KV, `isNewClient_watcher`);
`cache.New` (`New.spec` at the adapter's model, the default configuration); a context
(`WithCancel(Background())`); the cache's watch of the prefix from revision `2` (`Cache.Watch.spec`,
with one of `New`'s watch slots, its "open" token, and the main thread's token, back from the
server's start); the log `w` under its mutex (`wsInvF` at `okFactKM`), the writer goroutines (a
wait group; a client of the KV sending a write at most once, `client.isKv_of_newClient`; each put
with the adapter's write update, which keeps the plan's fact, `wk_put_W`, its logged fact
`okFactKM_of_write`), the
log's Puts `oks` taken under the lock, `maxRev`, `collect` (the cache watch's log, `log_ck`), the
cancel, and the check: `CheckOk` from `collectOk` and the Puts' `okFactKM`s
(`etcdstart.checkOk_of_km`), after (2026-11-03) a progress notification (`RequestProgress` with a
second watch slot's demux handle, `awaitProgress`: not past the events, `log_ck_progress`) and
`checkProgress`. Then (2026-11-02) the cache's `Get` of the prefix at the highest
revision `m` (`Cache.Get.spec` with one of `New`'s readers, `WithTimeout(Background())`'s context):
its error is non-nil (`cacheGetErr_ne_nil`) and ends `Main` with `GetFailed`; its answer is
etcd's state under the prefix at `m` (`cacheGetOk`), which passes `checkGet` (`getCheck_km`, over
`collect`'s facts and the adapter's invariant). Every start step's error ends `Main` with
`Failed`; `collect`'s `false` with `WatchEnded`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WatchSrv
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.cache.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.GenAll
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writer
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MaxRev
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.cache.collect
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Check
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.Writes
public import Proof.go_etcd_io.etcd.client.v3.KvOfNew
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartPeriodicServer
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.NoDup
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc
public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Spec.context.ErrAny
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.watcher__RequestProgress
public import Spec.go_etcd_io.etcd.cache.v3.New
public import Spec.go_etcd_io.etcd.cache.v3.Cache__Watch
public import Spec.go_etcd_io.etcd.cache.v3.Cache__Get
public import Spec.context.WithTimeoutBackground
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.cache.checkGet
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.GetFacts
public import Spec.go_etcd_io.etcd.cache.v3.Cache__RequestProgress
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.cache.awaitProgress
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.cache.checkProgress
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.sync.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.context.Results
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NoRefusal
public import Proof.go_etcd_io.etcd.client.v3.KMClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Boot
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.watch.Served
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_cache

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.cache.Assumptions]

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
/-- The cache's `Get` options (`WithPrefix()`, `WithRev(m)`): the range of the prefix, at revision
`m`; `OpGet` does not panic. -/
theorem ckGet_opts (m : w64) :
    (opGetModel ckPfx [withPrefixM, withRevM m]).base.rangeEnd = prefixRangeEnd ckPfx ∧
      (opGetModel ckPfx [withPrefixM, withRevM m]).base.rev = m ∧
      ¬ opGetPanics [withPrefixM, withRevM m] := by
  have h : ckPfx ≠ [] := by decide
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [opGetModel, opGetPanics, op_simps, h]

omit package_sem in
/-- The cache watch's options (`WithPrefix()`, `WithRev(2)`): the range of the prefix, from
revision `2`; `OpWatch` does not panic. -/
theorem ckWatch_opts :
    (opWatchModel ckPfx [withPrefixM, withRevM (W64 2)]).base.rangeEnd = prefixRangeEnd ckPfx ∧
      (opWatchModel ckPfx [withPrefixM, withRevM (W64 2)]).base.rev = W64 2 ∧
      ¬ opWatchPanics ckPfx [withPrefixM, withRevM (W64 2)] := by
  have h : ckPfx ≠ [] := by decide
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [opWatchModel, opWatchPanics, OpFull.watchPanics, op_simps, h]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
theorem Main.wp_proof
    (wp_GenAll : etcdstart.GenAll.spec (GF := GF) (hG := hG))
    (wp_Writer : etcdstart.Writer.spec (GF := GF) (hG := hG))
    (wp_MaxRev : etcdstart.MaxRev.spec (GF := GF) (hG := hG))
    (wp_collect : collect.spec (GF := GF) (hG := hG))
    (wp_Check : etcdstart.Check.spec (GF := GF) (hG := hG))
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartPeriodicServer : etcdstart.StartPeriodicServer.spec (GF := GF) (hG := hG))
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_RP : watcher.RequestProgress.spec (GF := GF) (hG := hG))
    (wp_CNew : ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EM : EtcdModel GF],
      EtcdGrove.New.spec (GF := GF) (hG := hG))
    (wp_CWatch : ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EM : EtcdModel GF],
      Cache.Watch.spec (GF := GF) (hG := hG))
    (wp_CGet : ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EM : EtcdModel GF],
      Cache.Get.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_checkGet : checkGet.spec (GF := GF) (hG := hG))
    (wp_CRP : ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EM : EtcdModel GF],
      Cache.RequestProgress.spec (GF := GF) (hG := hG))
    (wp_awaitProgress : awaitProgress.spec (GF := GF) (hG := hG))
    (wp_checkProgress : checkProgress.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) (hP : mvcc.api.persistent.law (GF := GF))
    (hR : mvcc.api.mvccState_reachable.law (GF := GF)) (hRS : mvcc.api.mvccReaders_split.law (GF := GF)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS CRE CEC N id ctxs boot nw nops Hbf Htb Hrb48 HrbN HwbN Hck Haf
    Hbuq Hrf Hdbo Hms hAs H0 H31 Hops Hmul
  have Htb31 : threadBound GF ≤ 2 ^ 31 := by omega
  wp_start as ⟨Hstart, Htok, #Hprem⟩
  -- (hub step 7) the client address's listen right, out of the member's start bundle (to `Serve`)
  icases etcdstart.memberStartRes_client _ _ _ rfl $$ Hstart with ⟨Haddr, Hstart⟩
  iunfold premises at Hprem
  iunfold etcdstart.premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Hsetlg, #Htd, #Hns, #Hnrl⟩
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
  -- `tried := etcdstart.GenAll(nw*nops, keys)`: the Puts, picked before the member starts
  have hmul : sint.Z (nw * nops) = sint.Z nw * sint.Z nops := by
    have h1 : 0 ≤ sint.Z nw * sint.Z nops := Int.mul_nonneg H0 Hops
    word
  (try wp_auto)
  wp_apply wp_slice_literal (l := genKeys)
  isplitr
  · ipureintro; rfl
  iintro %ksl ⟨Hks, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
    show max (max (3 : Int) 0) 0 = 3 from rfl]
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  (try wp_auto)
  wp_apply (wp_GenAll (nw * nops) _ genKeys (by rw [hmul]; exact Int.mul_nonneg H0 Hops)
      (by decide) (by decide)) as %tsl ⟨%trs, Htrs, %Htrs⟩
  · iframe #
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
  have hsz : ∀ p ∈ trs, etcdstart.wkvSizeOk p := fun p hp =>
    etcdstart.GenKv.sizeOk (by decide) (Htrs.2 p hp)
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
  -- the ghost state `NewServer` takes (`alloc1`)
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (etcdstart.alloc1_false hne id ctxs boot Hbf.idLow Hbf.boot Hbf.cc Hbf.urls (ckDir id) (dirOne_member id _)
      (by omega) (by omega) (cmp := true)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog, -, hkr⟩ := Hal
  -- (D48) the adapter's invariant over the KV state's half, at the plan's fact: the bootstrap log
  -- changes no KV state (`linkv.kvRaftOf_boot`), so the start state's changes are `[[]]`
  have hσ0 : (kvModelSt ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0))).changes = [[]] := by
    unfold kvModelSt kvModel
    rw [linkv.kvRaftOf_boot _ _ _ (fun _ _ => True) _ (LogEntry.toEntries boot 0) (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog]
    rfl
  imod (client.kmInv_alloc ρ.rd.kv _ (etcd_watch.wkW (trs.map pairOf))
      (by rw [hσ0]; exact etcd_watch.wkW_start _)) $$ Hetcd with ⟨%γk, %Hγk, #Hkm, #Hl0⟩
  rw [hσ0]
  obtain ⟨hγkv, hγW⟩ := Hγk
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- `Main`'s premises in the shared start's form
  ihave #Hb := etcdstart.bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (ckDir id) go!"cachekv" go!"cachekv"
      (etcdstart.urls1 go!"cachekv" go!"127.0.0.1:23883" go!"127.0.0.1:23873") id cfgOk urlsOk
      (fun _ h => h)
      (fun _ h => h) $$ Hboot
  ihave #Hcom : etcdstart.commonPremises (GF := GF) $$ []
  · iunfold etcdstart.commonPremises; iframe #
  -- `StartPeriodicServer("cachekv", peerAddr, clientAddr, period, lg)` (the cache over a
  -- compacting member, 2026-11-02: periodic mode at 10ms, the cluster's retention `0`)
  -- (2026-10-24, rafthttp stage 6d) the one-member directory is well formed
  have Hdirok : netDirOk (ckDir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  -- (hub step 7) no peer address: the start bundle is the fresh bundle at the network `γn`
  ihave Hfresh := etcdstart.memberStartRes_fresh _ _ γn rfl $$ Hstart
  wp_apply (wp_StartPeriodicServer N go!"cachekv" go!"127.0.0.1:23883" go!"127.0.0.1:23873"
      (W64 10000000) lg (LogEntry.toEntries boot 0) ctxs
      (ckDir id) id γ ρ E₀ Φs γn .none Htb
      Hrb48 HrbN HwbN hvs hrule hboot hblen hγn1 hγn2 Hdirok
      (by simp [ckDir, etcdstart.dir1, dirOne]) (rafthttp.bootCfg_dirOne id _) (by decide) Hlg (by decide) hkr Hck Haf Hbuq Hdbo)
    $$ [Htok Hmb Hfresh] as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Herr
  wp_auto
  icases etcdstart.memberUp_served _ _ _ _ _ _ _ $$ Hup with ⟨%E, %cfg, %γw, %HE, #Hreq, #Hrd, #Hsf,
    Hgo, Hlg3, Hbemu, HWR, ⟨Hlts, Hlgs, Hrds, Hsts, Hrslots, Hbms⟩, -, -⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HE
  -- `Serve(s, clientAddr)`, with the ghost step `wk_served_nd` (the KV specs and the watch server's
  -- facts at the address), the member refusal-free (D29) first
  haveI := Hms
  ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off srv E { ρ with wait := γw } ρ.rd
    $$ []
  · iframe #
  wp_apply (wp_Serve srv go!"127.0.0.1:23873" E { ρ with wait := γw } ρ.rd cfg
      (fun cid mid R => iprop(⌜R.E = E ∧ noRefusalAt go!"127.0.0.1:23873"⌝ ∗
        client.kvRegsAt (⟨go!"127.0.0.1:23873", E, ρ.rd, cid, mid⟩ : client.SrvAt GF) ∗
        watchAddrFacts (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23873" [] null null ckPfx null ρ.rd.kv) ∗
        srvGoRes srv)))
    $$ [Haddr Hlg3 Hbemu Hgo HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    isplitr
    · ipureintro; exact ⟨by rw [HElg]; exact Hlg, HEtr, HEw, Hms, Hbuq, HsvOff.2⟩
    iintro %gs %lis %cid %mid %R Hg
    rw [HsvOff.1]
    ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
    iunfold etcdstart.grpcUp at Hg
    icases Hg with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC,
      #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, Hgo2, HWRs, Hlis, -⟩
    obtain ⟨HCA, HCE, Hregs1, Hregs2, hRs, hRE, hRw, hRγ⟩ := HC
    -- the watch server's environment is the server's: `E` is `R.E` from here on
    subst hRE
    icases replicate_take2 _ _ (by omega) $$ Hlts with ⟨-, -, Hlts⟩
    icases replicate_take2 _ _ (by omega) $$ Hrds with ⟨Hrd1, -, Hrds⟩
    ihave Hslots := client.etcdGrpcSlots_of_started srv R.E ρ.rd 1 (64 - 2) 64
        etcdstart.memberReadN 64 (by omega) (by omega)
        etcdstart.one_le_memberReadN
        (by omega)
        $$ [Hlts Hlgs Hrds Hsts Hrslots Hbms]
    · iframe
    -- (D23) one watch run slot: two of the watchable store's readers, one of the request path's
    icases (hRS R.E.γ 2 62).1 $$ HWRs with ⟨HWR2, -⟩
    ihave Hwslots := client.watchRunSlots_of hRS R (etcdstart.srvWOf R.E ρ.rd false) 1 1 (Nat.le_refl _)
        $$ [HWR2 Hrd1]
    · simp only [etcdstart.srvWOf, Nat.mul_one]
      iframe HWR2
      isplitl [Hrd1]
      · simp only [List.replicate]
        iapply BigSepL.bigSepL_cons.2
        iframe Hrd1
        iapply BigSepL.bigSepL_nil.2; itrivial
      ipureintro
      rw [sync.rwmutex.actualMaxReaders_unseal]
      omega
    -- the watch server's facts: the members' KV facts (`srvKVFacts`, D47), `io.EOF`
    ihave #Hinvs := srvKVInvs_of_read srv R.E ρ.rd $$ Hrd
    ihave #Hkf : client.srvKVFacts
        (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23873" [] null null ckPfx null ρ.rd.kv) $$ []
    · iapply client.srvKVFacts_of_off _ ρ.rd (kvSame_refl _) hlog (by omega) rfl rfl
      iexact Hinvs
    ihave #Hkva := client.kvServerAt_of_is p srv C.A cid mid C.n $$ Hkvs
    rw [HCA]
    -- (D29) the member never refuses: authentication off, a voter (the members' axiom)
    ihave ⟨Hgsn, Hlis, %Hnr⟩ := (EtcdGrove.etcd_noRefusal go!"127.0.0.1:23873" gs q p srv lis R.E
        { ρ with wait := γw } [il, im, iu] [ims, is] svcs regs sregs Hregs1 HEo) $$
      [Hgsn Hlis]
    · iframe Hgsn Hlis; iframe #
    -- (the cache over a compacting member, 2026-11-02) the store's fact for watches: no revision
    -- writes a key twice (the writers' plan, `kmInv`'s `wkW`)
    -- the watch path's server facts (R9) and the watch condition
    ihave HWok : v3rpc.srvWOk (etcdstart.srvWOf R.E ρ.rd false) R.wsl v3rpc.wsN $$ []
    · rw [hRw]
      iapply (etcdstart.srvWOk_of_up hP hR srv R.E ρ.rd cfg C (by omega))
      iframe #
    ihave #HWau : kvReadAu ρ.rd.kv (fun σ => iprop(⌜etcd_watch.wkW (trs.map pairOf) σ.changes⌝)) $$ []
    · rw [← hγW, ← hγkv]; iapply client.kmWAu γk $$ Hkm
    ihave #Hon := etcd_cache.srvOnce_of_wk
        (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23873" [] null null ckPfx null ρ.rd.kv)
        ρ.rd.kv rfl (trs.map pairOf) $$ [Hkf HWau]
    · iframe #
    imod (etcd_watch.wk_served_nd hP (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23873" [] null null ckPfx null ρ.rd.kv) go!"127.0.0.1:23873"
        gs q p pw srv lis R.E { ρ with wait := γw } ρ.rd cid mid C.n il im iu ims is svcs regs sregs
        1 1 Hregs1 rfl rfl (by simp) rfl Hms.watch_impl Hregs2 rfl rfl rfl Hrf)
      $$ [Hgsn Hlis Hslots Hwslots HWok] with ⟨Hserv, #HKV, #HWF⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb48
    imodintro
    iframe Hserv HKV HWF Hgo2
    ipureintro; exact ⟨rfl, Hnr⟩
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, ⟨%HRQ, #HKV, #HWF, Hgo2⟩⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Hserr
  wp_auto
  obtain ⟨hRE, Hnr⟩ := HRQ
  -- the watch server's environment is the server's: `E` is `R.E` from here on
  subst hRE
  ihave #Hinvs := srvKVInvs_of_read srv R.E ρ.rd $$ Hrd
  -- `NewClient(clientAddr, lg)` (etcd's default client configuration, its default retries)
  wp_apply (wp_NewClient go!"127.0.0.1:23873" lg
      (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23873" [] null null ckPfx null ρ.rd.kv) Hlg
      (by unfold plainEndpoint; decide) Htb31) as %cl %cerr Hcl
  icases Hcl with (⟨%Hcerr, #Hnc, -⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Hcerr
  wp_auto
  -- (D29) a write sent at most once: the member is refusal-free
  ihave #Hwo : client.clientWriteOnce (GF := GF) cl [go!"127.0.0.1:23873"] $$ []
  · iunfold client.clientWriteOnce; ipureintro
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
    subst ha; exact Hnr
  -- the cache's client (`isEtcdClient`) at the adapter's model (D48): `clientv3.New`'s `KV`, a
  -- client of the KV from the member's registrations (`isKv_of_regs`), and its `Watcher`, a watcher
  -- of the KV (`isNewClient_watcher`, with the watch server's facts)
  ihave ⟨%w, %conn, %wc, %lgw, %ics, #HWa, #Hcw⟩ := isNewClient_watcher wp_ErrAny hAs cl
    [go!"127.0.0.1:23873"] (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23873" [] null null ckPfx null ρ.rd.kv) rfl
    rfl rfl rfl $$ [Pcli Ppb Pctx Hnc HWF]
  · iframe #
  ihave #Hnc' := Hnc
  iunfold isNewClient at Hnc'
  icases Hnc' with ⟨-, -, ⟨%api, #HKVa, #Hkvo⟩, -⟩
  imod (client.isKv_of_regs api [go!"127.0.0.1:23873"] R.E ρ.rd cid mid γk.kv (by rw [hγkv]; exact kvSame_refl _)
      (by omega)) $$ [Hkvo] with #Hisk
  · iframe Hkvo
    iapply client.kvRegs_one
    iexact HKV
  -- the writers' client of the KV, sending a write at most once
  imod (client.isKv_of_newClient cl [(⟨go!"127.0.0.1:23873", R.E, ρ.rd, cid, mid⟩ : client.SrvAt GF)] [go!"127.0.0.1:23873"]
      (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23873" [] null null ckPfx null ρ.rd.kv) γk.kv rfl
      (fun _ hx => by simp only [List.mem_singleton] at hx; subst hx; exact (by rw [hγkv]; exact kvSame_refl _)) (by omega)) $$ [Hnc Hwo HKV] with ⟨%apiw, #Hkvfw, #Hkvw⟩
  · iframe #
    iapply BigSepL.bigSepL_nil.2; itrivial
  ihave #Hkw : client.isKvWatcher w γk.kv $$ []
  · unfold client.isKvWatcher
    iexists _
    iframe Hcw
    ipureintro; rw [hγkv]
  ihave #Hecl := client.isEtcdClient_of_km cl w api γk true ckPfx (by decide)
    (show prefixRangeEnd ckPfx ≠ [W8 0] by decide) $$ []
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
  haveI : ThreadBoundLe GF (2 ^ 31 - cacheWgOwedMax) := ⟨by unfold cacheWgOwedMax; omega⟩
  wp_apply (wp_CNew (EM := client.etcdModelOfKV γk) cl ckPfx slice.nil []) $$ []
    as %c %cerr Hnew
  · iframe #
    isplitr
    · ipureintro; intro _; exact cfgDefault_bounded
    ipureintro; have : ckPfx.length = 3 := rfl; omega
  irevert Hnew
  unfold newCacheResult
  rw [if_pos cfgDefault_valid]
  iintro Hnew
  icases Hnew with ⟨%Hcerr, %cf, %γrd, %γd, %γnn, #Hcf, %Hcfe, Hhandles⟩
  subst Hcerr
  (try wp_auto)
  iunfold cacheHandles at Hhandles
  icases Hhandles with ⟨Hrds, Hslots, -, -, Hopen⟩
  -- one of the cache's readers, for its `Get`
  ihave ⟨Hcrd, -⟩ : cacheReader (EM := client.etcdModelOfKV γk) cf ∗ True $$ [Hrds]
  · have hmr : maxReaders - 1 = (maxReaders - 2) + 1 := by
      have := sync.actualMaxReaders_ge_2
      unfold maxReaders
      rw [sync.rwmutex.actualMaxReaders_unseal] at *
      omega
    rw [hmr]
    simp only [List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hrds with ⟨Hr, -⟩
    iframe Hr
  -- two of `New`'s watch slots: the watch's, and the demux handle `RequestProgress` needs
  ihave ⟨Hslot, Hslot2, -⟩ : cacheWatchSlot (EM := client.etcdModelOfKV γk) cf γd
      (sint.nat (cfgApply [] defaultConfigVal).HistoryWindowSize') ∗
    cacheWatchSlot (EM := client.etcdModelOfKV γk) cf γd
      (sint.nat (cfgApply [] defaultConfigVal).HistoryWindowSize') ∗ True $$ [Hslots]
  · have hmr : maxReaders - 2 = (maxReaders - 4) + 1 + 1 := by
      unfold maxReaders
      rw [sync.rwmutex.actualMaxReaders_unseal]
      decide
    rw [hmr]
    simp only [List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hslots with ⟨Hs, Hslots⟩
    icases BigSepL.bigSepL_cons.1 $$ Hslots with ⟨Hs2, -⟩
    iframe Hs Hs2
  icases cacheWatchSlot_parts (EM := client.etcdModelOfKV γk) _ _ _ $$ Hslot2 with ⟨Hdh, -⟩
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
  wp_apply (wp_CWatch (EM := client.etcdModelOfKV γk) c cf γrd γd _ wctx
      ({ Values := ∅, Deadline := none, Done_gn := γc, PDone := iprop(True) } :
        context.ContextDesc (IProp GF)) ckPfx optsSl
      ([withPrefixM, withRevM (W64 2)] : List (OpFull → OpFull)) 1)
    $$ [Hslot Hopen Htok] as %wch ⟨Hopen, Htok, %γw, #Hwch, Hcons⟩
  · iframe; iframe #
    ipureintro; exact ckWatch_opts.2.2
  have hre : (withPrefixM (OpFull.getInit ckPfx)).base.rangeEnd = prefixRangeEnd ckPfx := by
    have h : ckPfx ≠ [] := by decide
    simp [op_simps, h]
  rw [hre, Hcfe.1]
  (try wp_auto)
  icases typedPointsto_split _ _ _ $$ «$r0» with Hr0
  try simp only [TypedPointsto.typedPointstoDef]
  icases Hr0 with ⟨mu, ok, -⟩
  imod sync.init_Mutex (etcdstart.wsInvF «$r0_ptr» (etcdstart.okFactKM γk)) ⊤
      (structFieldRef github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes go!"Mu" «$r0_ptr»)
    $$ mu [ok] with #Hmu
  · inext
    iunfold etcdstart.wsInvF
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
      wp_apply (wp_Writer cl apiw γk.kv
          (fun k v => client.kmWriteQ γk [[]] (.put (client.putKeyOp k v)))
          (etcdstart.okFactKM γk) «$r0_ptr» tsl trs (k * nops) (k * nops + nops)
          (fun _ => inferInstance) hAs
          (by rw [hlo]; exact Int.mul_nonneg Hk.1 Hops) (by rw [hlo, hhi]; omega)
          (by
            rw [hhi, Htrs.1]
            have h2 : (sint.Z k + 1) * sint.Z nops ≤ sint.Z nw * sint.Z nops :=
              Int.mul_le_mul_of_nonneg_right (by omega) Hops
            rw [Int.add_mul, Int.one_mul] at h2
            have h0 : (0 : Int) ≤ sint.Z (nw * nops) := by
              rw [hmul]; exact Int.mul_nonneg H0 Hops
            have e : ((sint.nat (nw * nops) : Nat) : Int) = sint.Z (nw * nops) := by word
            rw [e, hmul]
            omega) hsz) $$ []
      · iframe #
        isplitr
        · iintro !> %k' %v' %hkv
          ihave Hw := client.km_write_au γk [[]] (.put (client.putKeyOp k' v'))
            (wk_put_W γk _ hγW k' v' hkv) $$ [$Hkm $Hl0]
          iunfold kvOpAu1 at Hw
          iunfold kvAu1 at Hw
          rw [show putWireOf (opPutModel k' v' []) = client.putKeyOp k' v' from rfl]
          iexact Hw
        iintro !> %k' %v' %σ HQ %Hb
        iapply (etcdstart.okFactKM_of_write γk k' v' σ) $$ HQ
        ipureintro; exact Hb
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
  wp_apply (sync.Mutex.wp_Lock (structFieldRef github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes
      go!"Mu" «$r0_ptr») (etcdstart.wsInvF «$r0_ptr» (etcdstart.okFactKM γk))) $$ [] as ⟨Hown, Hws0⟩
  · iframe #
  iunfold etcdstart.wsInvF at Hws0
  icases Hws0 with ⟨%osl, %oks, Hok, Hos, Hocap, #Hoks⟩
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Unlock (structFieldRef github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes
      go!"Mu" «$r0_ptr») (etcdstart.wsInvF «$r0_ptr» (etcdstart.okFactKM γk))) $$ [Hown Hok]
  · iframe #
    iframe Hown
    inext
    iunfold etcdstart.wsInvF
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
  wp_apply (wp_MaxRev osl oks (DFrac.own 1)) $$ [Hos] as %m ⟨Hos, %Hm⟩
  · iframe
  wp_apply (wp_collect γk (trs.map pairOf) wch γw (prefixRangeEnd ckPfx) m hγW hpk
      hkeys) $$ [Hcons]
    as %esl0 %ok0 Hcol
  · iframe; iframe #
  (try wp_auto)
  cases ok0
  · -- the watch ended before it reported every successful Put: `cancel()`
    (try wp_auto)
    wp_apply Hcancel $$ [] as -
    · itrivial
    (try wp_auto)
    iapply HΦ; ipureintro; right; right; left; rfl
  ihave ⟨%evs0, %rs, %Hrs, Hes0, Hecap0, Hcons, Hcok0⟩ := Hcol $$ %rfl
  (try wp_auto)
  -- `c.RequestProgress(wctx)`
  wp_apply (wp_CRP (EM := client.etcdModelOfKV γk) c cf γrd γd _ _) $$ [Hdh] as Hdh
  · iframe; iframe #
  (try wp_auto)
  -- `p, evs, ok := awaitProgress(wch, evs)`, then `cancel()`
  wp_apply (wp_awaitProgress γk (trs.map pairOf) wch γw (prefixRangeEnd ckPfx) m esl0 evs0 rs
      hγW hpk hkeys Hrs.1 Hrs.2) $$ [Hcons Hes0 Hecap0 Hcok0]
    as %p %esl %ok Hap
  · iframe; iframe #
  (try wp_auto)
  wp_apply Hcancel $$ [] as -
  · itrivial
  (try wp_auto)
  cases ok
  · -- the watch ended before a progress notification
    (try wp_auto)
    iapply HΦ; ipureintro; right; right; left; rfl
  ihave ⟨%evs, Hes, Hcok, %Hp⟩ := Hap $$ %rfl
  icases etcdstart.collectOk_elim _ _ _ _ $$ Hcok with ⟨%Hcp, #Hcr⟩
  imod ownSlice_persist _ _ _ $$ Hes with #Hes
  (try wp_auto)
  -- `checkProgress(evs, p)`
  wp_apply (wp_checkProgress esl evs p (fun i e h => (Hcp.2.2 i e h).2.1) Hp) $$ []
  · iframe #
  (try wp_auto)
  ihave %HCk := etcdstart.checkOk_of_km γk trs m evs oks Hm.2 $$ []
  · iframe Hoks
    iapply (etcdstart.collectOk_intro _ _ _ _ Hcp) $$ Hcr
  imod ownSlice_persist _ _ _ $$ Hos with #Hos
  (try wp_auto)
  wp_apply (wp_Check go!"cachekv" go!"Put" esl tsl osl evs trs oks HCk) $$ []
  · iframe #
  (try wp_auto)
  -- `if r != 0`: the cache's Get of the prefix at `r`
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ; ipureintro; left; rfl
  · have hm0 : m ≠ W64 0 := by simpa using Hif
    have hm1 : 1 ≤ sint.Z m := by
      have h0 := Hm.1
      have : sint.Z m ≠ 0 := fun h => hm0 (by word)
      omega
    have hme : sint.Z m ≤ 1 + evs.length := by
      rcases Hcp.1 with h | h
      · exact absurd h hm0
      · exact h
    -- `gctx, gcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
    wp_apply context.wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, #Hgic⟩
    (try wp_auto)
    -- the Get's options: the prefix at revision `r`
    wp_apply wp_WithPrefix as %g1 #Hg1
    wp_apply wp_WithRev m as %g2 #Hg2
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %gsl ⟨Hgsl, -⟩
    ipersist Hgsl
    (try wp_auto)
    generalize hgsl : slice.mk gsl _ _ = gOptsSl
    have hgfs : ([g1, zero_val GoFunc].set (sint.nat (W64 (0 + 1))) g2) = [g1, g2] := rfl
    ihave #Hgopts : optsAt gOptsSl ([withPrefixM, withRevM m] : List (OpFull → OpFull)) $$ []
    · iunfold optsAt
      iexists _
      iframe Hgsl
      isplitr
      · ipureintro; rw [hgfs]; rfl
      imodintro
      iintro %i %f %g %Hf %Hg
      rw [hgfs] at Hf
      rcases i with _ | _ | i
      · cases Hf; cases Hg; iexact Hg1
      · cases Hf; cases Hg; iexact Hg2
      · simp at Hf
    imod monoNatLbOwn_0 (GF := GF) cf.γs.rev with #Hlb0
    obtain ⟨hgre, hgrev, hgnp⟩ := ckGet_opts m
    -- `gresp, err := c.Get(gctx, prefix, ...)`
    wp_apply (wp_CGet (EM := client.etcdModelOfKV γk) c cf γrd γd _ (W64 0) gctx gcd ckPfx gOptsSl
        ([withPrefixM, withRevM m] : List (OpFull → OpFull))) $$ [Hcrd]
      as %gresp %gerr ⟨Hcrd, Hgres⟩
    · iframe; iframe #
      isplitr
      · ipureintro; exact hgnp
      unfold storeRevLb; rw [show sint.nat (W64 0) = 0 from rfl]; iexact Hlb0
    (try wp_auto)
    -- `gcancel()`
    wp_apply Hgcancel
    (try wp_auto)
    icases cacheGetResult_cases (EM := client.etcdModelOfKV γk) _ _ _ _ _ _ _ $$ Hgres with (⟨%Hnull, Hgerr⟩ | ⟨%Hgnil, Hgok⟩)
    · -- an error: `GetFailed`
      ihave #Prpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
      · iPkgInit
      ihave %Hne := cacheGetErr_ne_nil (EM := client.etcdModelOfKV γk) cf (W64 0) gcd ckPfx _
        gerr $$ Pcache Prpc Hgerr
      cases gerr with
      | nil => exact absurd rfl Hne
      | ok e =>
        wp_auto
        iapply HΦ; ipureintro; right; right; right; rfl
    · -- the answer: etcd's state under the prefix at `r`, which passes `checkGet`
      subst Hgnil
      icases cacheGetOk_rev (EM := client.etcdModelOfKV γk) _ _ _ _ _ hm0 $$ Hgok with ⟨%hdr, %kvsSl, %m', Hresp, Hkvs, Hkcap, Hst⟩
      irevert Hst
      rw [Hcfe.1]
      iintro Hst
      imod getCheck_km γk (trs.map pairOf) hγW evs m m'
          (fun i e h => ⟨(Hcp.2.2 i e h).2.1, (Hcp.2.2 i e h).2.2⟩) hpk hm1 hme
        $$ Hkm Hcr Hst with ⟨%s, %Hs, #Hv⟩
      obtain ⟨HCG, Hlen, Hrange⟩ := Hs
      irevert Hkvs
      try simp only []
      rw [hre, Hrange]
      iintro Hkvs
      imod ownSlice_persist _ _ _ $$ Hkvs with #Hkvs
      ihave #Hhold := kvsHold_of_vals m' s Hlen $$ Hv
      wp_auto
      wp_apply (wp_checkGet esl evs m kvsSl (m'.map Prod.snd) s HCG) $$ []
      · iframe #
      (try wp_auto)
      iapply HΦ; ipureintro; left; rfl

end proof

end etcd_cache
end EtcdGrove
end Perennial
