/-
Proof of `Spec/.../dist/client/RunCache.lean` (#50 F6, `notes/etcd-dist-plan.md` §29). Lean-first (no Rocq
counterpart).

The cache example's `Main` (`Proof/.../cache/Main.lean`) after its start, at the cluster's KV, with the watch
workload's adapter and writers (`RunWatch.lean`): `GenAll` picks the writers' Puts `trs` under `ck/`; the
clients' adapter over the share's client half (`client.kmInv_alloc`, the plan's property `wkW (trs.map
pairOf)`, true of the boot's changes `[[]]`); `newClient` (its failure ends the workload, `ended`); the
client is the cache's at the adapter's model (`isEtcdClient_of_dist`: its gets by `KV_GetE_dist`, its
watches by `Watch_dist`, its progress requests by `RequestProgress_dist`, all hypotheses); `cache.New` at
the default configuration (`New.spec`; its error ends the workload) and `defer c.Close()` (`Cache.Close`,
with the cache's whole "open" token, which the watch gives back); `WithCancel(Background())` and its
`defer cancel()`; the cache's watch of `ck/` from revision `2` (`Cache.Watch`, with one of `New`'s watch
slots, the "open" token and the machine's thread token); `ready()`; the writers at their machines
(`remoteWriters.spec`, a hypothesis: each successful Put's `okFactK` at the adapter); the timer
(`AfterFunc`; `defer t.Stop()`); `MaxRev`; `cacheCollect` (the cache watch's log, the cache example's
`log_ck`, at the adapter's plan, `wkW_eq`); `c.RequestProgress` with a second watch slot's demux handle;
`awaitProgress`; the cancel; `checkProgress`; `Check` (`CheckOk` from `collectOk` and the Puts' facts,
`etcdstart.checkOk_of_km`); and the cache's `Get` of `ck/` at the highest successful Put's revision under
a timeout (`Cache.Get` with one of `New`'s readers; its error ends the workload), whose answer is etcd's
state under the prefix there (`cacheGetOk_rev`), which passes `checkGet` (`getCheck_km`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunCache
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.remoteWriters
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.cacheCollect
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.awaitProgress
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checkProgress
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checkGet
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.GenAll
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MaxRev
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Check
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.cache.v3.New
public import Spec.go_etcd_io.etcd.cache.v3.Cache__Watch
public import Spec.go_etcd_io.etcd.cache.v3.Cache__Get
public import Spec.go_etcd_io.etcd.cache.v3.Cache__RequestProgress
public import Spec.go_etcd_io.etcd.cache.v3.Cache__Close
public import Spec.context.WithTimeoutBackground
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WritesKM
public import Perennial.Spec.time.AfterFunc
public import Perennial.Spec.time.Timer__Stop
public import Perennial.Proof.context.Link
public import Perennial.Proof.context.Results
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.cache.v3
open etcd_dist etcdstart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
theorem RunCache.wp_proof
    (wp_GenAll : etcdstart.GenAll.spec (GF := GF) (hG := hG))
    (wp_newClient : newClient.spec (GF := GF) (hG := hG))
    (wp_ended : ended.spec (GF := GF) (hG := hG))
    (wp_checked : checked.spec (GF := GF) (hG := hG))
    (wp_Get : KV_GetE_dist.spec (GF := GF) (hG := hG))
    (wp_Watch : Watch_dist.spec (GF := GF) (hG := hG))
    (wp_RP : RequestProgress_dist.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_CNew : ∀ [EM : EtcdModel GF], EtcdGrove.New.spec (GF := GF) (hG := hG))
    (wp_CWatch : ∀ [EM : EtcdModel GF], Cache.Watch.spec (GF := GF) (hG := hG))
    (wp_CRP : ∀ [EM : EtcdModel GF], Cache.RequestProgress.spec (GF := GF) (hG := hG))
    (wp_CGet : ∀ [EM : EtcdModel GF], Cache.Get.spec (GF := GF) (hG := hG))
    (wp_CClose : ∀ [EM : EtcdModel GF], Cache.Close.spec (GF := GF) (hG := hG))
    (wp_remoteWriters : remoteWriters.spec (GF := GF) (hG := hG))
    (wp_AfterFunc : time.AfterFunc.spec (GF := GF) (hG := hG))
    (wp_Stop : time.Timer.Stop.spec (GF := GF) (hG := hG))
    (wp_MaxRev : etcdstart.MaxRev.spec (GF := GF) (hG := hG))
    (wp_cacheCollect : cacheCollect.spec (GF := GF) (hG := hG))
    (wp_awaitProgress : awaitProgress.spec (GF := GF) (hG := hG))
    (wp_checkProgress : checkProgress.spec (GF := GF) (hG := hG))
    (wp_Check : etcdstart.Check.spec (GF := GF) (hG := hG))
    (wp_checkGet : checkGet.spec (GF := GF) (hG := hG)) :
    RunCache.spec (GF := GF) (hG := hG) := by
  intro π ρ eps nodes addrs ns nops ready hV Htb hpl H0 H56 Hmul hAs
  wp_start as ⟨Htok, #Heps, #Hnodes, #Hready, Hsh⟩
  iunfold cacheShare at Hsh
  iunfold watchShare at Hsh
  icases Hsh with ⟨%Γ, %σ₀, %Hσ0, #Hms, Hkv, HWS⟩
  have Htb31 : threadBound GF ≤ 2 ^ 31 := by omega
  ihave #Hcci : _root_.Perennial.context.isClosedchanInit (GF := GF) $$ []
  · iapply _root_.Perennial.context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pes : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Pcache : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 $$ []
  · iPkgInit
  ihave #Hall := client.ctxErrClientAllW_of wp_ErrAny hAs $$ Pctx
  ihave %Hnl := ownSlice_len $$ Hnodes
  have hnl : (ns.length : Int) = sint.Z nodes.len := by have := Hnl.1; word
  have hmul : sint.Z (nodes.len * nops) = ns.length * sint.Z nops := by
    have h1 : 0 ≤ sint.Z nodes.len * sint.Z nops := Int.mul_nonneg (by have := Hnl.2; word) H0
    have h2 : sint.Z nodes.len * sint.Z nops < 2 ^ 63 := by rw [← hnl]; exact Hmul
    rw [hnl]
    word
  icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, Htok1⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  -- `tried := etcdstart.GenAll(len(nodes) * nops, keys)`
  wp_apply wp_slice_literal (l := ckKeys)
  isplitr
  · ipureintro; rfl
  iintro %ksl ⟨Hks, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
    show max (max (3 : Int) 0) 0 = 3 from rfl]
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  (try wp_auto)
  wp_apply (wp_GenAll (nodes.len * nops) _ ckKeys
      (by rw [hmul]; exact Int.mul_nonneg (by omega) H0) (by decide) (by decide))
    as %tsl ⟨%trs, Htrs, %Htrs⟩
  · iframe #
  imod ownSlice_persist _ _ _ $$ Htrs with #Htrs
  have hpk := ck_genKeys_pfx trs Htrs.2
  have hkeys := ck_genKeys_range trs Htrs.2
  have hps : ∀ p ∈ trs, pairOf p ∈ trs.map pairOf ∧ wkvSmall p := fun p hp =>
    ⟨List.mem_map_of_mem hp, ck_genKv_small p (Htrs.2 p hp)⟩
  have htl : (trs.length : Int) = ns.length * sint.Z nops := by
    have h0 : 0 ≤ sint.Z (nodes.len * nops) := by rw [hmul]; exact Int.mul_nonneg (by omega) H0
    rw [Htrs.1, ← hmul]; word
  -- the clients' adapter over the cluster's KV, its property the plan's
  have hW0 : etcd_partition.wkW (trs.map pairOf) σ₀.changes := by
    rw [Hσ0]; exact etcd_partition.wkW_start _
  imod (kmInv_alloc Γ.kv σ₀ (etcd_partition.wkW (trs.map pairOf)) hW0) $$ Hkv
    with ⟨%γ, %Hγ, #Hkm, #Hlb0⟩
  obtain ⟨hγk, hγW⟩ := Hγ
  have hγeq : kmOf Γ (γ.ch, γ.tok, trs.map pairOf) = γ := by
    cases γ; simp only at hγk hγW; simp [kmOf, hγk, hγW]
  have hγW' : γ.W = etcd_watch.wkW (trs.map pairOf) := by rw [hγW, wkW_eq]
  ihave #Hlb : monoListLbOwn γ.ch ([[]] : List (List mvcc.Change)) $$ []
  · rw [← Hσ0]; iexact Hlb0
  (try wp_auto)
  -- `ccli, err := newClient(eps)`
  wp_apply (wp_newClient eps addrs (Classical.choice hV) Htb hpl) $$ [$Hlt] as %cl %cerr ⟨Hlt, Hcl⟩
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, #Hnp⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ
    iapply (threadTok_level0 (GF := GF)).2
    iframe
  subst Hcerr
  -- the client: a KV client and a watch client of the view, so the cache's at the adapter's model
  ihave ⟨%w, #Hwc⟩ := watchClient_of_new cl addrs (Classical.choice hV) Γ $$ [Hnc Hnp Hms]
  · iframe #
  ihave ⟨%api, #Hkc⟩ := kvClient_of_new cl addrs (Classical.choice hV) Γ $$ [Hnc Hnp Hms]
  · iframe #
  ihave #Hecl := isEtcdClient_of_dist wp_Get wp_Watch wp_RP cl api w addrs (Classical.choice hV) Γ γ
    hγk etcd_cache.ckPfx (by decide) (by decide) $$ [Pcli Ppb Pctx Hall Hkc Hwc Hkm]
  · iframe #
  (try wp_auto)
  -- `c, err := cache.New(ccli, cachePrefix)`: the default configuration
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
  wp_apply (wp_CNew (EM := client.etcdModelOfKV γ) cl etcd_cache.ckPfx slice.nil []) $$ []
    as %c %cerr Hnew
  · iframe #
    isplitr
    · ipureintro; intro _; exact ck_cfgDefault_bounded
    ipureintro; have : etcd_cache.ckPfx.length = 3 := rfl; omega
  irevert Hnew
  unfold newCacheResult
  rw [if_pos ck_cfgDefault_valid]
  iintro Hnew
  icases Hnew with ⟨%Hcerr, %cf, %γrd, %γd, %γnn, #Hcf, %Hcfe, Hhandles⟩
  subst Hcerr
  (try wp_auto)
  iunfold cacheHandles at Hhandles
  icases Hhandles with ⟨Hrds, Hslots, -, -, Hopen⟩
  -- one of the cache's readers, for its `Get`
  ihave ⟨Hcrd, -⟩ : cacheReader (EM := client.etcdModelOfKV γ) cf ∗ True $$ [Hrds]
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
  ihave ⟨Hslot, Hslot2, -⟩ : cacheWatchSlot (EM := client.etcdModelOfKV γ) cf γd
      (sint.nat (cfgApply [] defaultConfigVal).HistoryWindowSize') ∗
    cacheWatchSlot (EM := client.etcdModelOfKV γ) cf γd
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
  icases cacheWatchSlot_parts (EM := client.etcdModelOfKV γ) _ _ _ $$ Hslot2 with ⟨Hdh, -⟩
  -- `defer c.Close()`: the defer chain, which needs the cache's whole "open" token
  ihave ⟨%dv, defer, #Hdv⟩ : iprop(∃ dv : GoFunc, defer ↦ dv ∗
      □ (∀ Ψ : val → IProp GF, cacheOpen (GF := GF) cf 1 -∗ ▷ (True -∗ Ψ #()) -∗
        WP (App (Val #dv) (Val #())) {{ Ψ }})) $$ [defer]
  · iexists _
    iframe defer
    iintro !> %Ψ Hop HΨ
    wp_auto
    wp_apply (wp_CClose (EM := client.etcdModelOfKV γ) c cf γrd γd _) $$ [Hop] as -
    · iframe; iframe #
    (try wp_auto)
    iapply HΨ
    (try itrivial)
  (try wp_auto)
  -- `wctx, cancel := context.WithCancel(context.Background())`, `defer cancel()`
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Pctx $Hcci]
    as %wctx %γc %cancel ⟨#Hcancel, #Hwctx, -, #Hwfrom⟩
  (try wp_auto)
  ihave ⟨%dv', defer, #Hdv'⟩ : iprop(∃ dv' : GoFunc, defer ↦ dv' ∗
      □ (∀ Ψ : val → IProp GF, cacheOpen (GF := GF) cf 1 -∗ ▷ (True -∗ Ψ #()) -∗
        WP (App (Val #dv') (Val #())) {{ Ψ }})) $$ [defer]
  · iexists _
    iframe defer
    iintro !> %Ψ Hop HΨ
    wp_auto
    wp_apply Hcancel $$ [] as -
    · itrivial
    (try wp_auto)
    wp_apply Hdv $$ [Hop]
    · iexact Hop
    (try wp_auto)
    iapply HΨ
    (try itrivial)
  iclear Hdv
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
  -- `wch := c.Watch(wctx, cachePrefix, ...)`: the cache's watch contract, from revision `2`
  ihave Htok := (threadTok_level0 (GF := GF)).2 $$ [Hlt Htok1]
  · iframe
  wp_apply (wp_CWatch (EM := client.etcdModelOfKV γ) c cf γrd γd _ wctx
      ({ Values := ∅, Deadline := none, Done_gn := γc, PDone := iprop(True) } :
        context.ContextDesc (IProp GF)) etcd_cache.ckPfx optsSl
      ([withPrefixM, withRevM (W64 2)] : List (OpFull → OpFull)) 1)
    $$ [Hslot Hopen Htok] as %wch ⟨Hopen, Htok, %γw, #Hwch, Hcons⟩
  · iframe; iframe #
    ipureintro; exact ck_watch_opts.2.2
  have hre : (withPrefixM (OpFull.getInit etcd_cache.ckPfx)).base.rangeEnd =
      prefixRangeEnd etcd_cache.ckPfx := by
    have h : etcd_cache.ckPfx ≠ [] := by decide
    simp [op_simps, h]
  rw [hre, Hcfe.1]
  icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, Htok1⟩
  (try wp_auto)
  -- `ready()`
  wp_apply Hready
  (try wp_auto)
  -- `oks := remoteWriters(nodes, tried, nops)`
  wp_apply (wp_remoteWriters nodes tsl ns trs nops Γ (γ.ch, γ.tok, trs.map pairOf) Htb H0 H56 htl hps)
    $$ [$Hlt HWS] as %okSl ⟨Hlt, %oks, Hos, #Hoks0⟩
  · rw [hγeq]
    iframe #
    iframe
  ihave #Hoks : □ [∗list] p ∈ oks, okFactKM (GF := GF) γ p $$ []
  · have hfe : etcd_partition.okFactK (GF := GF) γ = okFactKM γ := by
      funext p; unfold etcd_partition.okFactK okFactKM kmRevAt etcd_partition.revAtK; rfl
    ihave #Hoks1 : □ [∗list] p ∈ oks, etcd_partition.okFactK (GF := GF) γ p $$ []
    · rw [← hγeq]; iexact Hoks0
    rw [← hfe]
    iexact Hoks1
  (try wp_auto)
  -- `t := time.AfterFunc(readTimeout, cancel)`, `defer t.Stop()`
  wp_apply (wp_AfterFunc _ cancel) $$ [] as %t #Ht
  · wp_apply Hcancel $$ [] as -
    · itrivial
    ipureintro; exact isPanic_intoVal ()
  (try wp_auto)
  ihave ⟨%dv'', defer, #Hdv''⟩ : iprop(∃ dv'' : GoFunc, defer ↦ dv'' ∗
      □ (∀ Ψ : val → IProp GF, cacheOpen (GF := GF) cf 1 -∗ ▷ (True -∗ Ψ #()) -∗
        WP (App (Val #dv'') (Val #())) {{ Ψ }})) $$ [defer]
  · iexists _
    iframe defer
    iintro !> %Ψ Hop HΨ
    wp_auto
    wp_apply (wp_Stop t) $$ [] as %b -
    · iright; iexact Ht
    (try wp_auto)
    wp_apply Hdv' $$ [Hop]
    · iexact Hop
    (try wp_auto)
    iapply HΨ
    (try itrivial)
  iclear Hdv'
  -- `r := etcdstart.MaxRev(oks)`; `evs, ok := cacheCollect(wch, r)`
  wp_apply (wp_MaxRev okSl oks (DFrac.own 1)) $$ [Hos] as %m ⟨Hos, %Hm⟩
  · iframe
  (try wp_auto)
  wp_apply (wp_cacheCollect γ (trs.map pairOf) wch γw (prefixRangeEnd etcd_cache.ckPfx) m hγW' hpk
      hkeys) $$ [Hcons]
    as %esl0 %ok0 Hcol
  · iframe; iframe #
  (try wp_auto)
  cases ok0
  · -- the watch ended before it reported every successful Put
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    wp_apply Hdv'' $$ [Hopen]
    · iexact Hopen
    (try wp_auto)
    iapply HΦ
    iapply (threadTok_level0 (GF := GF)).2
    iframe
  ihave ⟨%evs0, %rs, %Hrs, Hes0, Hecap0, Hcons, Hcok0⟩ := Hcol $$ %rfl
  (try wp_auto)
  -- `c.RequestProgress(wctx)`
  wp_apply (wp_CRP (EM := client.etcdModelOfKV γ) c cf γrd γd _ _) $$ [Hdh] as Hdh
  · iframe; iframe #
  (try wp_auto)
  -- `p, evs, ok := awaitProgress(wch, evs)`, then `cancel()`
  wp_apply (wp_awaitProgress γ (trs.map pairOf) wch γw (prefixRangeEnd etcd_cache.ckPfx) m esl0 evs0 rs
      hγW' hpk hkeys Hrs.1 Hrs.2) $$ [Hcons Hes0 Hecap0 Hcok0]
    as %p %esl %ok Hap
  · iframe; iframe #
  (try wp_auto)
  wp_apply Hcancel $$ [] as -
  · itrivial
  (try wp_auto)
  cases ok
  · -- the watch ended before a progress notification
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    wp_apply Hdv'' $$ [Hopen]
    · iexact Hopen
    (try wp_auto)
    iapply HΦ
    iapply (threadTok_level0 (GF := GF)).2
    iframe
  ihave ⟨%evs, Hes, Hcok, %Hp⟩ := Hap $$ %rfl
  icases etcdstart.collectOk_elim _ _ _ _ $$ Hcok with ⟨%Hcp, #Hcr⟩
  imod ownSlice_persist _ _ _ $$ Hes with #Hes
  (try wp_auto)
  -- `checkProgress(evs, p)`
  wp_apply (wp_checkProgress esl evs p (fun i e h => (Hcp.2.2 i e h).2.1) Hp) $$ []
  · iframe #
  (try wp_auto)
  ihave %HCk := etcdstart.checkOk_of_km γ trs m evs oks Hm.2 $$ []
  · iframe Hoks
    iapply (etcdstart.collectOk_intro _ _ _ _ Hcp) $$ Hcr
  imod ownSlice_persist _ _ _ $$ Hos with #Hos
  (try wp_auto)
  wp_apply (wp_Check go!"dist cache" go!"Put" esl tsl okSl evs trs oks HCk) $$ []
  · iframe #
  (try wp_auto)
  -- `if r != 0`: the cache's Get of the prefix at `r`
  wp_if_destruct
  · (try wp_auto)
    wp_apply wp_checked as %r -
    (try wp_auto)
    wp_apply Hdv'' $$ [Hopen]
    · iexact Hopen
    (try wp_auto)
    iapply HΦ
    iapply (threadTok_level0 (GF := GF)).2
    iframe
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
      as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, #Hgic, #HgC⟩
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
    imod monoNatLbOwn_0 (GF := GF) cf.γs.rev with #Hlb0'
    obtain ⟨hgre, hgrev, hgnp⟩ := ck_get_opts m
    -- `gresp, err := c.Get(gctx, cachePrefix, ...)`
    wp_apply (wp_CGet (EM := client.etcdModelOfKV γ) c cf γrd γd _ (W64 0) gctx gcd etcd_cache.ckPfx
        gOptsSl ([withPrefixM, withRevM m] : List (OpFull → OpFull))) $$ [$Hlt Hcrd]
      as %gresp %gerr ⟨Hlt, Hcrd, Hgres⟩
    · iframe; iframe #
      isplitr
      · ipureintro; exact hgnp
      unfold storeRevLb; rw [show sint.nat (W64 0) = 0 from rfl]; iexact Hlb0'
    (try wp_auto)
    -- `gcancel()`
    wp_apply Hgcancel
    (try wp_auto)
    icases cacheGetResult_cases (EM := client.etcdModelOfKV γ) _ _ _ _ _ _ _ $$ Hgres with
      (⟨%Hnull, Hgerr⟩ | ⟨%Hgnil, Hgok⟩)
    · -- an error: the workload ends
      ihave #Prpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
      · iPkgInit
      ihave %Hne := cacheGetErr_ne_nil (EM := client.etcdModelOfKV γ) cf (W64 0) gcd etcd_cache.ckPfx _
        gerr $$ Pcache Prpc Hgerr
      cases gerr with
      | nil => exact absurd rfl Hne
      | ok e =>
        wp_auto
        wp_apply wp_ended as %r -
        (try wp_auto)
        wp_apply Hdv'' $$ [Hopen]
        · iexact Hopen
        (try wp_auto)
        iapply HΦ
        iapply (threadTok_level0 (GF := GF)).2
        iframe
    · -- the answer: etcd's state under the prefix at `r`, which passes `checkGet`
      subst Hgnil
      icases cacheGetOk_rev (EM := client.etcdModelOfKV γ) _ _ _ _ _ hm0 $$ Hgok with
        ⟨%hdr, %kvsSl, %m', Hresp, Hkvs, Hkcap, Hst⟩
      irevert Hst
      rw [Hcfe.1]
      iintro Hst
      imod etcd_cache.getCheck_km γ (trs.map pairOf) hγW' evs m m'
          (fun i e h => ⟨(Hcp.2.2 i e h).2.1, (Hcp.2.2 i e h).2.2⟩) hpk hm1 hme
        $$ Hkm Hcr Hst with ⟨%s, %Hs, #Hv⟩
      obtain ⟨HCG, Hlen, Hrange⟩ := Hs
      irevert Hkvs
      try simp only []
      rw [hre, Hrange]
      iintro Hkvs
      imod ownSlice_persist _ _ _ $$ Hkvs with #Hkvs
      ihave #Hhold := etcd_cache.kvsHold_of_vals m' s Hlen $$ Hv
      wp_auto
      ihave #Hhold' : kvsHold (GF := GF) (m'.map Prod.snd) s $$ []
      · iunfold kvsHold
        iunfold etcd_cache.kvsHold at Hhold
        iexact Hhold
      wp_apply (wp_checkGet esl evs m kvsSl (m'.map Prod.snd) s HCG) $$ []
      · iframe #
      (try wp_auto)
      wp_apply wp_checked as %r -
      (try wp_auto)
      wp_apply Hdv'' $$ [Hopen]
      · iexact Hopen
      (try wp_auto)
      iapply HΦ
      iapply (threadTok_level0 (GF := GF)).2
      iframe

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
