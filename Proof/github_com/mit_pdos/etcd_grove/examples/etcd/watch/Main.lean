/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/watch/Main.lean` (D23, 2026-10-20).
Lean-first (no Rocq counterpart).

`genAll` picks the writers' Puts `trs` first. The server's start is the examples' shared one
(since 2026-10-22, D33): `etcdstart.alloc1`, then watchkv's invariant over the KV state's half
(`wkInv_alloc` at the plan `trs.map pairOf`: the bootstrap log changes no KV state,
`linkv.kvRaftOf_boot`; `Writes.lean`), `etcdstart.StartServer`, `etcdstart.Serve` with the ghost step: the gRPC run pools
(`etcdstart.kvServeStocks_pools`), the member refusal-free (`etcd_noRefusal`, D29), and `wk_served`
(`Served.lean`: the KV methods and the watch server's facts at the address, the members' KV facts
`srvKVFacts` from the server's read path). Then `etcdstart.NewClient` (etcd's default configuration;
`clientWriteOnce`, D29), and from here on the program sees etcd through the client's KV and watch
specs only (2026-10-26; until then through the clients' model of etcd, D48): the client's `KV` a
client of the KV (`isKv`, `client.isKv_of_newClient`), its `Watcher` (`isNewClient_watcher`) a
watcher of it (`isKvWatcher`); a context (`WithCancel(Background())`), the prefix watch from
revision `1` (`watcher.Watch.spec`, its options as the cache's `watchEvents_opts`, with the read
update `wk_read_au`), the log `w` under its mutex (`wsInvF` at `okFactW`), the writer goroutines
(a wait group; each put with the update `wk_write_au`, its logged fact `okFactW_of_write`), the
log's Puts `oks` taken under the lock, `maxRev`, `collect` (each response read from the KV state,
its events the plan's puts, `resp_state`), the cancel, and the check: `CheckOk` from `collectOk`
and the Puts' `okFactW`s (`checkOk_of_wk`). Every start step's error ends `Main` with `Failed`; `collect`'s `false`
with `WatchEnded`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WatchSrv
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.watch.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.GenAll
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writer
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MaxRev
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Collect
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.CollectPlan
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Check
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.watch.StateResp
public import Proof.go_etcd_io.etcd.client.v3.KvOfNew
public import Proof.go_etcd_io.etcd.client.v3.Link
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc
public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Spec.context.ErrAny
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WithProgressNotify
public import Spec.go_etcd_io.etcd.client.v3.WithCreatedNotify
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.sync.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.context.Results
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NoRefusal
public import Proof.go_etcd_io.etcd.cache.v3.Cache__watchEvents
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.watch.Served
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Boot
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 6400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_watch

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.watch.Assumptions]

set_option maxHeartbeats 1600000 in
theorem Main.wp_proof
    (wp_GenAll : etcdstart.GenAll.spec (GF := GF) (hG := hG))
    (wp_Writer : etcdstart.Writer.spec (GF := GF) (hG := hG))
    (wp_MaxRev : etcdstart.MaxRev.spec (GF := GF) (hG := hG))
    (wp_Collect : etcdstart.Collect.spec (GF := GF) (hG := hG))
    (wp_Check : etcdstart.Check.spec (GF := GF) (hG := hG))
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartServer : etcdstart.StartServer.spec (GF := GF) (hG := hG))
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_WithProgressNotify : WithProgressNotify.spec (GF := GF) (hG := hG))
    (wp_WithCreatedNotify : WithCreatedNotify.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) (hP : mvcc.api.persistent.law (GF := GF))
    (hR : mvcc.api.mvccState_reachable.law (GF := GF)) (hRS : mvcc.api.mvccReaders_split.law (GF := GF)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS CRE CEC N id ctxs boot nw nops Hbf Htb HLv Hrb48 HrbN HwbN Hck Haf
    Hbuq Hrf Hdbo Hms hAs H0 H31 Hops Hmul
  have Htb31 : threadBound GF ≤ 2 ^ 31 := by omega
  wp_start as ⟨Hstart, Htok, #Hprem⟩
  -- (hub step 7) the client address's listen right, out of the member's start bundle (to `Serve`)
  icases etcdstart.memberStartRes_client _ _ _ rfl $$ Hstart with ⟨Haddr, Hstart⟩
  iunfold premises at Hprem
  iunfold etcdstart.premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Htd, #Hns, #Hnrl⟩
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
  have hpk : ∀ kv ∈ trs.map pairOf, wkPfx <+: kv.1 := by
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
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  (try wp_auto)
  -- the ghost state `NewServer` takes (`alloc1`)
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (etcdstart.alloc1_false hne id ctxs boot Hbf (wkDir id) (dirOne_member id _)
      (by omega) (by omega)) $$ Hmarsh with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog, -⟩ := Hal
  -- (M2, the storage side, N1) the member's mode, off (read before `StartServer` takes the bundle)
  ihave ⟨%Hcmp0, Hmb⟩ := etcdstart.memberBoot_cmp γ ctxs ρ E₀ Φs id false $$ Hmb
  -- watchkv's invariant over the KV state's half, at the plan: the bootstrap log changes no KV
  -- state (`linkv.kvRaftOf_boot`), so the start state's changes are `[[]]`
  have hσ0 : (kvModelSt ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0))).changes = [[]] := by
    unfold kvModelSt kvModel
    rw [linkv.kvRaftOf_boot _ _ _ (fun _ _ => True) _ (LogEntry.toEntries boot 0) (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog]
    rfl
  imod (wkInv_alloc ρ.rd.kv _ (trs.map pairOf) (by rw [hσ0]; exact wkW_start _))
    $$ Hetcd with ⟨%γc, #Hwk⟩
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- `Main`'s premises in the shared start's form
  ihave #Hb := etcdstart.bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (wkDir id) go!"watchkv" go!"watchkv"
      (etcdstart.urls1 go!"watchkv" go!"127.0.0.1:23882" go!"127.0.0.1:23872") id cfgOk urlsOk
      (fun _ h => h)
      (fun _ h => h) $$ Hboot
  ihave #Hcom : etcdstart.commonPremises (GF := GF) $$ []
  · iunfold etcdstart.commonPremises; iframe #
  -- `StartServer("watchkv", peerAddr, clientAddr, lg)`
  -- (2026-10-24, rafthttp stage 6d) the one-member directory is well formed
  have Hdirok : netDirOk (wkDir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  -- (hub step 7) no peer address: the start bundle is the fresh bundle at the network `γn`
  ihave Hfresh := etcdstart.memberStartRes_fresh _ _ γn rfl $$ Hstart
  wp_apply (wp_StartServer N go!"watchkv" go!"127.0.0.1:23882" go!"127.0.0.1:23872" lg (LogEntry.toEntries boot 0) ctxs
      (wkDir id) id γ ρ E₀ Φs γn .none Htb
      Hrb48 HrbN HwbN hvs hrule hboot hblen hγn1 hγn2 Hdirok
      (by simp [wkDir, etcdstart.dir1, dirOne]) (rafthttp.bootCfg_dirOne id _) (by decide) Hck Haf Hbuq Hdbo)
    $$ [Htok Hmb Hfresh] as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup, -⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Herr
  wp_auto
  icases etcdstart.memberUp_served _ _ _ _ _ _ _ $$ Hup with ⟨%E, %cfg, %γw, %HE, #Hreq, #Hrd, #Hsf,
    Hgo, Hlg3, Hbemu, #Hwb, Hstk, -, -⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HE
  -- `Serve(s, clientAddr)`, with the ghost step `wk_served_nd` (the KV specs and the watch server's
  -- facts at the address), the member refusal-free (D29) first
  haveI := Hms
  ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off srv E { ρ with wait := γw } ρ.rd
    $$ []
  · iframe #
  ihave #HzlgC : zapLoggerOk cfg.Logger' $$ []
  · rw [HElg]; iexact Hlgz
  wp_apply (wp_Serve srv go!"127.0.0.1:23872" E { ρ with wait := γw } ρ.rd cfg
      (fun cid mid R => iprop(⌜R.E = E ∧ noRefusalAt go!"127.0.0.1:23872"⌝ ∗
        client.kvRegsAt (⟨go!"127.0.0.1:23872", E, ρ.rd, cid, mid⟩ : client.SrvAt GF) ∗
        watchAddrFacts (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23872" [] null null wkPfx null ρ.rd.kv))))
    $$ [Haddr Hlg3 Hbemu Hgo Hstk] as %serr Hs
  · iframe; iframe #
    isplitr
    · ipureintro; exact ⟨HEtr, HEw, Hms, Hbuq, HsvOff.2⟩
    iintro %gs %lis %cid %mid %R Hg
    rw [HsvOff.1]
    ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
    iunfold etcdstart.grpcUp at Hg
    icases Hg with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC,
      #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, -, Hlis, -⟩
    obtain ⟨HCA, HCE, Hregs1, Hregs2, hRs, hRE, hRw, hRγ, Hnd⟩ := HC
    -- the watch server's environment is the server's: `E` is `R.E` from here on
    subst hRE
    -- (per-type stage B3) the gRPC run pools, from the serving stocks
    imod (etcdstart.kvServeStocks_pools srv R.E ρ.rd ⊤) $$ Hstk with ⟨#Hrp, #Hrb⟩
    -- the watch server's facts: the members' KV facts (`srvKVFacts`, D47), `io.EOF`
    ihave #Hinvs := srvKVInvs_of_read srv R.E ρ.rd $$ Hrd
    ihave %Hcm : ⌜ρ.rd.kv.cmp = false⌝ $$ []
    · iunfold srvKVInvs at Hinvs
      icases Hinvs with ⟨-, -, -, -, %Hm, -⟩
      ipureintro; rw [Hm.1, HEa.2.2.2]; exact Hcmp0
    ihave #Hkf : client.srvKVFacts
        (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23872" [] null null wkPfx null ρ.rd.kv) $$ []
    · iapply client.srvKVFacts_of_off _ ρ.rd (kvSame_refl _) hlog (by omega) rfl rfl
      iexact Hinvs
    ihave #Hkva := client.kvServerAt_of_is p srv C.A cid mid C.n $$ Hkvs
    rw [HCA]
    -- (D29) the member never refuses: authentication off, a voter (the members' axiom)
    ihave ⟨Hgsn, Hlis, %Hnr⟩ := (EtcdGrove.etcd_noRefusal go!"127.0.0.1:23872" gs q p srv lis R.E
        { ρ with wait := γw } [il, im, iu] [ims, is] svcs regs sregs Hregs1 HEo) $$
      [Hgsn Hlis]
    · iframe Hgsn Hlis; iframe #
    -- the watch path's server facts and the watch condition (the cluster never compacts)
    ihave HWok : v3rpc.srvWOk (etcdstart.srvWOf R.E ρ.rd false) R.wsl v3rpc.wsN $$ []
    · rw [hRw]
      iapply (etcdstart.srvWOk_of_up hP hR srv R.E ρ.rd cfg C (by omega))
      iframe #
    ihave #Hon := client.srvOnce_noCmp (etcdstart.srvWOf R.E ρ.rd false) ρ.rd rfl Hcm
    imod (wk_served_nd hP (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23872" [] null null wkPfx null ρ.rd.kv) go!"127.0.0.1:23872"
        gs q p pw srv lis R.E { ρ with wait := γw } ρ.rd cid mid C.n il im iu ims is svcs regs sregs
        Hregs1 rfl rfl hRs rfl (by simp) rfl Hms.watch_impl Hregs2 rfl rfl rfl Hrf Hnd
        (by rw [sync.rwmutex.actualMaxReaders_unseal]; omega) HLv)
      $$ [Hgsn Hlis HWok] with ⟨Hserv, #HKV, #HWF⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb48
    imodintro
    iframe Hserv HKV HWF
    ipureintro; exact ⟨rfl, Hnr⟩
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, ⟨%HRQ, #HKV, #HWF⟩⟩)
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
  wp_apply (wp_NewClient go!"127.0.0.1:23872" lg
      (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23872" [] null null wkPfx null ρ.rd.kv)
      (by unfold plainEndpoint; decide) Htb31) as %cl %cerr Hcl
  · iframe #
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
  ihave #Hwo : client.clientWriteOnce (GF := GF) cl [go!"127.0.0.1:23872"] $$ []
  · iunfold client.clientWriteOnce; ipureintro
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
    subst ha; exact Hnr
  -- the client's `KV`: a client of etcd's KV, sending a write at most once
  imod (client.isKv_of_newClient cl [(⟨go!"127.0.0.1:23872", R.E, ρ.rd, cid, mid⟩ : client.SrvAt GF)] [go!"127.0.0.1:23872"]
      (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23872" [] null null wkPfx null ρ.rd.kv) ρ.rd.kv rfl
      (fun _ hx => by simp only [List.mem_singleton] at hx; subst hx; exact kvSame_refl _) (by omega)) $$ [Hnc Hwo HKV] with ⟨%api, #Hkvf, #Hkv⟩
  · iframe #
    iapply BigSepL.bigSepL_nil.2; itrivial
  -- the client's `Watcher`, with the watch server's facts (D19f): a watcher of etcd's KV
  ihave ⟨%w, %conn, %wc, %lgw, %ics, #HWf, #Hcw⟩ := isNewClient_watcher wp_ErrAny hAs cl
    [go!"127.0.0.1:23872"] (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23872" [] null null wkPfx null ρ.rd.kv) rfl
    rfl rfl rfl $$ [Pcli Ppb Pctx Hnc HWF]
  · iframe #
  ihave #Hkw : client.isKvWatcher w ρ.rd.kv $$ []
  · unfold client.isKvWatcher
    iexists _
    iframe Hcw
    ipureintro; rfl
  (try wp_auto)
  -- `wctx, cancel := context.WithCancel(context.Background())`
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Pctx $Hcci]
    as %wctx %γctx %cancel ⟨#Hcancel, #Hwctx, -, #wctxFrom⟩
  ihave #wctxO := metadata.outgoingCtxOkC_bgFrom wctx $$ wctxFrom
  (try wp_auto)
  -- the watch's options (the cache's `watchEvents`')
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_WithRev (W64 1) as %f2 #Hf2
  wp_apply wp_WithProgressNotify as %f3 #Hf3
  wp_apply wp_WithCreatedNotify as %f4 #Hf4
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  ipersist Hosl
  (try wp_auto)
  generalize hosl : slice.mk osl _ _ = optsSl
  have hfs : (([f1, zero_val GoFunc, zero_val GoFunc, zero_val GoFunc].set
      (sint.nat (W64 (0 + 1))) f2).set (sint.nat (W64 (0 + 1 + 1))) f3).set
      (sint.nat (W64 (0 + 1 + 1 + 1))) f4 = [f1, f2, f3, f4] := rfl
  ihave #Hopts : optsAt optsSl ([withPrefixM, withRevM (W64 1), withProgressNotifyM,
      withCreatedNotifyM] : List (OpFull → OpFull)) $$ []
  · iunfold optsAt
    iexists _
    iframe Hosl
    isplitr
    · ipureintro; rw [hfs]; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rw [hfs] at Hf
    rcases i with _ | _ | _ | _ | i
    · cases Hf; cases Hg; iexact Hf1
    · cases Hf; cases Hg; iexact Hf2
    · cases Hf; cases Hg; iexact Hf3
    · cases Hf; cases Hg; iexact Hf4
    · simp at Hf
  -- `wch := cli.Watcher.Watch(wctx, prefix, ...)`: the client's watch spec, from revision `1`,
  -- with the read update of watchkv's invariant
  obtain ⟨hpw, hnp⟩ := watchEvents_opts wkPfx (W64 1)
  unfold OpFull.isPrefixWatch at hpw
  simp only [decide_eq_true_eq, show wkPfx ≠ [] by decide, if_false] at hpw
  obtain ⟨ht, hr, -, -, hpv, hfr, hfp, hfd, hkey, hend⟩ := hpw
  ihave #Hau := wk_read_au ρ.rd.kv γc (trs.map pairOf) $$ Hwk
  iunfold kvReadAu at Hau
  iunfold kvAu at Hau
  -- (G2) the watcher's environment explicit, no auth bound (`n = 0`)
  wp_apply (wp_Watch w _ ρ.rd.kv wctx
      ({ Values := ∅, Deadline := none, Done_gn := γctx, PDone := iprop(True) } :
        context.ContextDesc (IProp GF))
      wkPfx optsSl
      ([withPrefixM, withRevM (W64 1), withProgressNotifyM, withCreatedNotifyM] :
        List (OpFull → OpFull))
      (W64 1) (wkReadQ γc (trs.map pairOf)) 0) $$ [] as %wch %γw ⟨#Hsp, Hcons, Hcur⟩
  · iframe #
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply EtcdGrove.context.watchCtx_of_isContext; isplitl [] <;> iassumption
    isplitr
    · ipureintro
      refine ⟨?_, hnp, by decide⟩
      unfold OpFull.isRangeWatch; simp only [decide_eq_true_eq]
      exact ⟨ht, hr, hpv, hfr, hfp, hfd⟩
    iintro !> %h
    exact absurd h.2 (Nat.lt_irrefl 0)
  -- (G2) a non-empty key's range is its own (`watchNorm_of_ne`)
  rw [OpFull.watchNorm_of_ne _ (by rw [hkey]; decide)]
  ihave #Hwch := etcdstart.isRespChan_of_state wch _ γw _ (wkReadQ γc (trs.map pairOf)) _ $$ Hsp
  (try wp_auto)
  -- the log of the successful Puts under its mutex (`wsInvF` at `okFactW`)
  icases typedPointsto_split _ _ _ $$ «$r0» with Hr0
  try simp only [TypedPointsto.typedPointstoDef]
  icases Hr0 with ⟨mu, ok, -⟩
  imod sync.init_Mutex (etcdstart.wsInvF «$r0_ptr» (okFactW γc)) ⊤
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
      wp_apply (wp_Writer cl api ρ.rd.kv (wkWriteQ γc (trs.map pairOf)) (okFactW γc) «$r0_ptr» tsl
          trs (k * nops) (k * nops + nops) (fun _ => inferInstance) hAs
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
          ihave Hw := wk_write_au ρ.rd.kv γc (trs.map pairOf) k' v' hkv $$ Hwk
          iunfold kvOpAu1 at Hw
          iunfold kvAu1 at Hw
          iexact Hw
        iintro !> %k' %v' %σ HQ %Hb
        iapply (okFactW_of_write γc (trs.map pairOf) k' v' σ) $$ HQ
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
      go!"Mu" «$r0_ptr») (etcdstart.wsInvF «$r0_ptr» (okFactW γc))) $$ [] as ⟨Hown, Hws0⟩
  · iframe #
  iunfold etcdstart.wsInvF at Hws0
  icases Hws0 with ⟨%osl, %oks, Hok, Hos, Hocap, #Hoks⟩
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Unlock (structFieldRef github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes
      go!"Mu" «$r0_ptr») (etcdstart.wsInvF «$r0_ptr» (okFactW γc))) $$ [Hown Hok]
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
  have h10 : (W64 1 - W64 1 : w64) = W64 0 := by decide
  ihave Hcons : etcdWatchConsumer γw 0 (W64 0) $$ [Hcons Hcur]
  · unfold etcdWatchConsumer
    iexists []
    rw [← h10]
    iframe Hcons Hcur
    ipureintro; rfl
  wp_apply (etcdstart.wp_Collect_plan wp_Collect (etcdstart.stateOk (opWatchModel wkPfx [withPrefixM, withRevM (W64 1), withProgressNotifyM, withCreatedNotifyM]) (wkReadQ γc (trs.map pairOf)))
      (wkRevAt γc) iprop(True) (trs.map pairOf) wch γw m (fun _ _ _ _ => inferInstance)
      (fun c c' v r => etcdstart.stateOk_closeErr _ _ c c' v r)
      (fun n c c' v r hne hcur => by
        iintro - Hok
        iapply (resp_state γc (trs.map pairOf) hpk (opWatchModel wkPfx [withPrefixM, withRevM (W64 1), withProgressNotifyM, withCreatedNotifyM]) hkey hend n c c' v r hne
          hcur) $$ Hok))
    $$ [Hcons] as %esl %ok Hcol
  · iframe; iframe #
    iintro !>; itrivial
  (try wp_auto)
  wp_apply Hcancel $$ [] as -
  · itrivial
  (try wp_auto)
  cases ok
  · -- the watch ended before it reported every successful Put
    (try wp_auto)
    iapply HΦ; ipureintro; right; right; rfl
  ihave ⟨%evs, Hes, Hcok⟩ := Hcol $$ %rfl
  ihave %HCk := checkOk_of_wk γc trs m evs oks Hm.2 $$ [Hcok]
  · iframe Hcok
    iexact Hoks
  imod ownSlice_persist _ _ _ $$ Hes with #Hes
  imod ownSlice_persist _ _ _ $$ Hos with #Hos
  (try wp_auto)
  wp_apply (wp_Check go!"watchkv" go!"Put" esl tsl osl evs trs oks HCk) $$ []
  · iframe #
  (try wp_auto)
  iapply HΦ; ipureintro; left; rfl

end proof

end etcd_watch
end EtcdGrove
end Perennial
