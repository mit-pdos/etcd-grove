/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/cachekv/Main.lean` (2026-10-20). Lean-first
(no Rocq counterpart).

watchkv's `Main` (`Proof/.../watchkv/Main.lean`, before 2026-10-26, when watchkv stopped using the
adapter) with the watch through etcd's cache: `genAll`
picks the writers' Puts `trs` first; the server's start is watchkv's, the examples' shared one
(`common.alloc1`; D48: the adapter's invariant over the KV state's half, `client.kmInv_alloc` at
the plan's fact `watchkv.wkW (trs.map pairOf)`; `common.StartServer`, `common.Serve` with one
watch run slot, `etcd_noRefusal` and `watchkv.wk_served` as the ghost step, D33). Then
`common.NewClient` (etcd's default configuration; the member refusal-free, so `clientWriteOnce`,
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
(`common.checkOk_of_km`). Every start step's error ends `Main` with `Failed`; `collect`'s `false`
with `WatchEnded`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.GenAll
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Writer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.MaxRev
public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.collect
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Check
public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.Writes
public import Proof.go_etcd_io.etcd.client.v3.KvOfNew
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Alloc
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
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NoRefusal
public import Proof.go_etcd_io.etcd.client.v3.KMClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Boot
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Served
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

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
    simp [opWatchModel, opWatchPanics, OpFull.watchPanics, op_simps, h]

set_option maxHeartbeats 1600000 in
theorem Main.wp_proof
    (wp_GenAll : common.GenAll.spec (GF := GF) (hG := hG))
    (wp_Writer : common.Writer.spec (GF := GF) (hG := hG))
    (wp_MaxRev : common.MaxRev.spec (GF := GF) (hG := hG))
    (wp_collect : collect.spec (GF := GF) (hG := hG))
    (wp_Check : common.Check.spec (GF := GF) (hG := hG))
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartServer : common.StartServer.spec (GF := GF) (hG := hG))
    (wp_Serve : common.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : common.NewClient.spec (GF := GF) (hG := hG))
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
  intro CS ES FS RS CRE CEC N id ctxs boot nw nops Hbf Htb Hrb48 HrbN Hck Haf
    Hbuq Hdbo Hms hAs H0 H31 Hops Hmul
  have Htb31 : threadBound GF ≤ 2 ^ 31 := by omega
  wp_start as ⟨Haddr, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Hsetlg, #Htd, #Hns, #Htk, #Hstop, #Hnrl⟩
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
  -- `tried := common.GenAll(nw*nops, keys)`: the Puts, picked before the member starts
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
  imod (common.alloc1 id ctxs boot Hbf.idLow Hbf.boot Hbf.cc (ckDir id) (dirOne_member id _)
      (by omega) (by omega)) $$ Hmarsh with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hvs, hdyn, hboot, hγn1, hγn2, hlog⟩ := Hal
  -- (D48) the adapter's invariant over the KV state's half, at the plan's fact: the bootstrap log
  -- changes no KV state (`linkv.kvRaftOf_boot`), so the start state's changes are `[[]]`
  have hσ0 : (kvModelSt ρ.rd.kv (bootEntries (Draft.LogEntry.toEntries boot 0))).changes = [[]] := by
    unfold kvModelSt kvModel
    rw [linkv.kvRaftOf_boot _ _ _ (fun _ _ => True) _ (Draft.LogEntry.toEntries boot 0) (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog]
    rfl
  imod (client.kmInv_alloc ρ.rd.kv _ (watchkv.wkW (trs.map pairOf))
      (by rw [hσ0]; exact watchkv.wkW_start _)) $$ Hetcd with ⟨%γk, %Hγk, #Hkm, #Hl0⟩
  rw [hσ0]
  obtain ⟨hγkv, hγW⟩ := Hγk
  have hblen : (Draft.LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [Draft.LogEntry.toEntries, hblen0]
  -- `Main`'s premises in the shared start's form
  ihave #Hb := common.bootPremise_of N [id] (Draft.LogEntry.toEntries boot 0) ctxs (ckDir id) go!"cachekv" go!"cachekv"
      (common.urls1 go!"cachekv" go!"127.0.0.1:23883" go!"127.0.0.1:23873") id cfgOk urlsOk
      (fun _ h => by obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h; exact ⟨h1, by rw [h2]; rfl, h3, h4, h5, h6⟩)
      (fun _ h => by obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, h2, h3, h4⟩) $$ Hboot
  ihave #Hcom : common.commonPremises (GF := GF) $$ []
  · iunfold common.commonPremises; iframe #
  -- `StartServer("cachekv", peerAddr, clientAddr, lg)`
  -- (2026-10-24, rafthttp stage 6d) the one-member directory is well formed
  have Hdirok : netDirOk (ckDir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  wp_apply (wp_StartServer N go!"cachekv" go!"127.0.0.1:23883" go!"127.0.0.1:23873" lg (Draft.LogEntry.toEntries boot 0) ctxs
      (ckDir id) id γ ρ E₀ Φs γn Htb31
      Hrb48 HrbN hvs hdyn hboot hblen hγn1 hγn2 Hdirok
      (by simp [ckDir, dirOne]) Hlg Hck Haf Hbuq Hdbo)
    $$ [Htok Hmb] as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HE, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, #Hwb, #Hsf, Hwpi,
    Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms, -, HWR⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HE
  -- `Serve(s, clientAddr)`, with the ghost step `wk_served` (the KV specs and the watch server's
  -- facts at the address), the member refusal-free (D29) first
  haveI := Hms
  wp_apply (wp_Serve srv go!"127.0.0.1:23873" E { ρ with wait := γw } ρ.rd cfg
      (fun cid mid R => iprop(⌜R.E = E ∧ noRefusalAt go!"127.0.0.1:23873"⌝ ∗
        client.kvRegsAt (⟨go!"127.0.0.1:23873", E, ρ.rd, cid, mid⟩ : client.SrvAt GF) ∗
        watchAddrFacts (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23873" [] null null ckPfx null ρ.rd.kv.st) ∗
        srvGoRes srv ∗ mvcc.idxCert R.E.γ.idx [[], []]))
      (by rw [HElg]; exact Hlg) HEtr HEw Hms Hbuq)
    $$ [Haddr Hlg3 Hbemu Hgo Hwpi HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    iintro %gs %lis %cid %mid %R Hg
    iunfold common.grpcUp at Hg
    icases Hg with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %d', %HC,
      #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, Hgo2, -, HWRs, Hlis⟩
    obtain ⟨HCA, HCE, Hregs1, Hregs2, hRs, hRE, hRw, hRγ⟩ := HC
    -- the watch server's environment is the server's: `E` is `R.E` from here on
    subst hRE
    icases replicate_take2 _ _ (by omega) $$ Hlts with ⟨-, -, Hlts⟩
    icases replicate_take2 _ _ (by omega) $$ Hrds with ⟨Hrd1, -, Hrds⟩
    ihave Hslots := client.etcdGrpcSlots_of_started srv R.E ρ.rd 1 (64 - 2) 64
        (Int.toNat sync.rwmutex.actualMaxReaders) 64 (by omega) (by omega)
        (by have := sync.actualMaxReaders_ge_2; omega) (by omega)
        $$ [Hlts Hlgs Hrds Hsts Hrslots Hbms]
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
    -- the watch server's facts: the members' KV facts (`srvKVFacts`, D47), `io.EOF`
    ihave #Hinvs := client.srvKVInvs_of_read srv R.E ρ.rd $$ Hrd
    ihave #H00 := watchkv.cert0_of_server pw R $$ Hws
    ihave #Hkf : client.srvKVFacts
        (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23873" [] null null ckPfx null ρ.rd.kv.st) $$ []
    · iunfold client.srvKVFacts
      iexists ρ.rd
      iframe Hinvs
      isplitl
      · iapply mvcc.idxCert_sealed; iexact H00
      ipureintro; exact ⟨rfl, hlog, by omega⟩
    ihave #Hkva := client.kvServerAt_of_is p srv C.A cid mid C.n $$ Hkvs
    rw [HCA]
    -- (D29) the member never refuses: authentication off, a voter (the members' axiom)
    ihave ⟨Hgsn, Hlis, %Hnr⟩ := (EtcdGrove.etcd_noRefusal go!"127.0.0.1:23873" gs q p srv lis R.E
        { ρ with wait := γw } [il, im, iu] [ims, is] svcs regs sregs Hregs1 HEo) $$
      [Hgsn Hlis]
    · iframe Hgsn Hlis; iframe #
    imod (watchkv.wk_served (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23873" [] null null ckPfx null ρ.rd.kv.st) go!"127.0.0.1:23873"
        gs q p pw srv lis R.E { ρ with wait := γw } ρ.rd cid mid C.n il im iu ims is svcs regs sregs
        1 1 Hregs1 rfl rfl (by simp) rfl Hms.watch_impl Hregs2 rfl rfl)
      $$ [Hgsn Hlis Hslots Hwslots] with ⟨Hserv, #HKV, #HWF⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb48
    imodintro
    iframe Hserv HKV HWF Hgo2 H00
    ipureintro; exact ⟨rfl, Hnr⟩
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, ⟨%HRQ, #HKV, #HWF, Hgo2, #H00⟩⟩)
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
  ihave #Hinvs := client.srvKVInvs_of_read srv R.E ρ.rd $$ Hrd
  -- `NewClient(clientAddr, lg)` (etcd's default client configuration, its default retries)
  wp_apply (wp_NewClient go!"127.0.0.1:23873" lg
      (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23873" [] null null ckPfx null ρ.rd.kv.st) Hlg
      (by unfold plainEndpoint; decide) Htb31) as %cl %cerr Hcl
  icases Hcl with (⟨%Hcerr, #Hnc⟩ | %Hcfail)
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
    [go!"127.0.0.1:23873"] (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23873" [] null null ckPfx null ρ.rd.kv.st) rfl
    rfl rfl $$ [Pcli Ppb Pctx Hnc HWF]
  · iframe #
  ihave #Hnc' := Hnc
  iunfold isNewClient at Hnc'
  icases Hnc' with ⟨-, -, ⟨%api, #HKVa, #Hkvo⟩, -⟩
  imod (client.isKv_of_regs api [go!"127.0.0.1:23873"] R.E ρ.rd cid mid γk.kv (by rw [hγkv])
      (by omega)) $$ [Hkvo] with #Hisk
  · iframe Hkvo
    iapply client.kvRegs_one
    iexact HKV
  -- the writers' client of the KV, sending a write at most once
  imod (client.isKv_of_newClient cl go!"127.0.0.1:23873"
      (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23873" [] null null ckPfx null ρ.rd.kv.st) R.E ρ.rd
      cid mid γk.kv (by rw [hγkv]) (by omega)) $$ [Hnc Hwo HKV] with ⟨%apiw, #Hkvfw, #Hkvw⟩
  · iframe #
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
  wp_apply (wp_CNew (EM := client.etcdModelOfKV γk) cl ckPfx slice.nil []) $$ []
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
  ihave ⟨Hslot, -⟩ : cacheWatchSlot (EM := client.etcdModelOfKV γk) cf γd
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
  imod sync.init_Mutex (common.wsInvF «$r0_ptr» (common.okFactKM γk)) ⊤
      (structFieldRef github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Mu" «$r0_ptr»)
    $$ mu [ok] with #Hmu
  · inext
    iunfold common.wsInvF
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
          (common.okFactKM γk) «$r0_ptr» tsl trs (k * nops) (k * nops + nops)
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
            omega)) $$ []
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
        iapply (common.okFactKM_of_write γk k' v' σ) $$ HQ
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
  wp_apply (sync.Mutex.wp_Lock (structFieldRef github_com.mit_pdos.etcd_grove.examples.common.Writes
      go!"Mu" «$r0_ptr») (common.wsInvF «$r0_ptr» (common.okFactKM γk))) $$ [] as ⟨Hown, Hws0⟩
  · iframe #
  iunfold common.wsInvF at Hws0
  icases Hws0 with ⟨%osl, %oks, Hok, Hos, Hocap, #Hoks⟩
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Unlock (structFieldRef github_com.mit_pdos.etcd_grove.examples.common.Writes
      go!"Mu" «$r0_ptr») (common.wsInvF «$r0_ptr» (common.okFactKM γk))) $$ [Hown Hok]
  · iframe #
    iframe Hown
    inext
    iunfold common.wsInvF
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
  ihave %HCk := common.checkOk_of_km γk trs m evs oks Hm.2 $$ [Hcok]
  · iframe Hcok
    iexact Hoks
  imod ownSlice_persist _ _ _ $$ Hes with #Hes
  imod ownSlice_persist _ _ _ $$ Hos with #Hos
  (try wp_auto)
  wp_apply (wp_Check go!"cachekv" go!"Put" esl tsl osl evs trs oks HCk) $$ []
  · iframe #
  (try wp_auto)
  iapply HΦ; ipureintro; left; rfl

end proof

end cachekv
end EtcdGrove
end Perennial
