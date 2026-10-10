/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/newCache.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.newCache
public import Spec.go_etcd_io.etcd.cache.v3.newStore
public import Spec.go_etcd_io.etcd.cache.v3.newReady
public import Spec.go_etcd_io.etcd.cache.v3.newConditionalProgressRequestor
public import Spec.go_etcd_io.etcd.cache.v3.NewDemux
public import Spec.go_etcd_io.etcd.cache.v3.Cache__getWatchLoop
public import Spec.go_etcd_io.etcd.cache.v3.conditionalProgressRequestor__run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem newCache.wp_proof
    (wp_newStore : newStore.spec (GF := GF) (hG := hG))
    (wp_newReady : newReady.spec (GF := GF) (hG := hG))
    (wp_newCPR : newConditionalProgressRequestor.spec (GF := GF) (hG := hG))
    (wp_NewDemux : NewDemux.spec (GF := GF) (hG := hG))
    (wp_getWatchLoop : Cache.getWatchLoop.spec (GF := GF) (hG := hG))
    (wp_run : conditionalProgressRequestor.run.spec (GF := GF) (hG := hG)) :
    newCache.spec (GF := GF) (hG := hG) := fun client pfx cfg clk => by
  wp_start as ⟨#Hcci, #Hcl, #Hclk, %Hcfg, %Hthr⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  have h0 : sint.Z (W64 0) = 0 := by decide
  have h2 : sint.Z (W64 2) = 2 := by decide
  wp_auto
  wp_if_destruct
  · -- `HistoryWindowSize <= 0`
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hfmt $Hsl] as %e -
    iapply HΦ
    unfold newCacheResult CfgValid
    have hn : ¬ (0 < sint.Z cfg.HistoryWindowSize' ∧ 2 ≤ sint.Z cfg.BTreeDegree') := by omega
    simp only [hn, ↓reduceIte]
    ipureintro
    exact ⟨trivial, fun h => by cases h⟩
  wp_if_destruct
  · -- `BTreeDegree < 2`
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hfmt $Hsl] as %e -
    iapply HΦ
    unfold newCacheResult CfgValid
    have hn : ¬ (0 < sint.Z cfg.HistoryWindowSize' ∧ 2 ≤ sint.Z cfg.BTreeDegree') := by omega
    simp only [hn, ↓reduceIte]
    ipureintro
    exact ⟨trivial, fun h => by cases h⟩
  have hvalid : CfgValid cfg := ⟨by omega, by omega⟩
  obtain ⟨hH, hB, hP⟩ := Hcfg hvalid
  -- the revision bound, at `0`
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γb, Hba, -⟩
  let R0 : w64 → IProp GF := fun r =>
    iprop(etcdReached r ∗ (⌜sint.Z r ≤ 0⌝ ∨ monoNatLbOwn γb (sint.nat r)))
  ihave #HstorePre : ⌜1 < sint.Z cfg.BTreeDegree' ∧ sint.Z cfg.BTreeDegree' ≤ 2 ^ 62⌝ ∗
      ⌜0 < sint.Z cfg.HistoryWindowSize' ∧ sint.Z cfg.HistoryWindowSize' ≤ 2 ^ 61⌝ ∗
      □ R0 (W64 0) $$ []
  · isplitl
    · ipureintro; constructor <;> omega
    isplitl
    · ipureintro; constructor <;> omega
    imodintro
    simp only [R0]
    isplitl
    · iapply etcdReached_zero
    · ileft; ipureintro; decide
  ihave #HdemuxPre : ⌜0 < sint.Z cfg.HistoryWindowSize' ∧ sint.Z cfg.HistoryWindowSize' ≤ 2 ^ 61⌝ $$ []
  · ipureintro; constructor <;> omega
  -- the internal context
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Hctxp $Hcci]
    as %ictx %γi %cancel ⟨#Hcancel, #Hictx, #Hcc⟩
  ihave #Hcancel := context.cancel_spec_forget _ _ _ $$ Hcancel
  -- the client's fields
  ihave #Hcl' := Hcl
  iunfold isEtcdClient at Hcl'
  icases Hcl' with ⟨%kv, %w, #HKVf, #HWf, #HisKV, #HisW, #HisPN, -, -⟩
  try wp_auto
  wp_apply wp_newStore (etcdCert pfx) R0 cfg.BTreeDegree' cfg.HistoryWindowSize'
    $$ [$Hpkg $HstorePre]
    as %st %γs ⟨#HisStore, #HisStoreW, #Hslb0, Hrds⟩
  wp_apply wp_newReady $$ [$Hpkg] as %rd %γr ⟨#HisReady, -⟩
  wp_apply wp_newCPR (GoInterface.ok w) (GoInterface.ok clk) cfg.ProgressRequestInterval' $$ [$Hpkg]
    as %pr ⟨#HisPR, #HprRun⟩
  iStructNamedPrefix «$r0» "C"
  -- the wait group, its counter invariant, the "open" token
  imod sync.init_WaitGroup cacheWgWGN (cacheWgAddr «$r0_ptr») $$ CwaitGroup
    with ⟨%γwg, #HisWg, Hwgo, Hwaiters⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γwr, Hwra⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γwb, Hwba⟩
  imod ownTokAuth_add cacheWgBudget γwb 0 $$ Hwba with ⟨Hwba, Hbud⟩
  imod ownToks_0 (GF := GF) γwb with Hbud0
  imod ownTokAuth_alloc (GF := GF) with ⟨%γwo, Hwoa⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γwc, Hwca⟩
  imod ownTokAuth_add cacheWgOwedMax γwc 0 $$ Hwca with ⟨Hwca, Hcaps⟩
  imod ownToks_0 (GF := GF) γwc with Hcap0
  ihave Htk0 : threadToks (GF := GF) 0 $$ []
  · iapply threadToks_zero
  imod ghostVar_alloc (GF := GF) () with ⟨%γop, Hop⟩
  obtain ⟨cfX, hX⟩ : ∃ x : CacheFields, x =
      { pfx := pfx, cfg := cfg, ready := rd, demux := null, store := st, γs := γs,
        scap := sint.nat cfg.HistoryWindowSize', kv := kv, pr := pr, watcher := w, ictx := ictx,
        clock := clk, γwg := γwg, γwb := γwb, γwr := γwr, γwo := γwo, γwc := γwc, stop := cancel,
        γop := γop, γb := γb } := ⟨_, rfl⟩
  imod inv_alloc cacheWgN ⊤ (cacheWgInv (GF := GF) cfX)
    $$ [Hwgo Hwaiters Hwra Htk0 Hwoa Hcap0 Hwca Hbud0 Hwba] with #HwgInv
  · inext
    subst hX
    unfold cacheWgInv
    iexists W32 0, 0, 0, 0
    rw [show sint.nat (W32 0) = 0 from rfl]
    iframe
    isplitr
    · ipureintro; decide
    isplitr
    · ipureintro; rfl
    ileft; ipureintro; rfl
  ihave #Hproto := cache_wgSlotProtocol «$r0_ptr» cfX Hthr $$ [$Hsync]
  · subst hX; iframe #
  -- one budget token for the resync loop, two for the watch loop and the progress requestor;
  -- the three owed capacities likewise
  rw [show cacheWgBudget = (2 ^ 31 - 4) + 3 from rfl]
  icases ownToks_add_1 3 (2 ^ 31 - 4) γwb $$ Hbud with ⟨Hbud, H3⟩
  icases ownToks_add_1 2 1 γwb $$ H3 with ⟨H1, H2⟩
  rw [show cacheWgOwedMax = 1 + 2 from rfl]
  icases ownToks_add_1 2 1 γwc $$ Hcaps with ⟨Hcap1, Hcap2⟩
  ihave Hslot1 : cacheWgSlot (GF := GF) cfX ∗ cacheWgOwedCap cfX ∗ cacheOpen cfX 1 $$ [H1 Hcap1 Hop]
  · subst hX; unfold cacheWgSlot cacheWgOwedCap cacheOpen; iframe
  -- `NewDemux`, which starts the resync loop
  wp_apply wp_NewDemux (cacheCert cfX) ictx _ (cacheWgAddr «$r0_ptr»)
    iprop(cacheWgSlot cfX ∗ cacheWgOwedCap cfX ∗ cacheOpen cfX 1) (cacheWgRunningOwed cfX)
    (cacheOpen cfX 1)
    cfg.HistoryWindowSize' cfg.ResyncInterval' $$ [$Hpkg $Hictx $HdemuxPre $Hproto $Hslot1]
    as %d %γd %γn ⟨Hop, #HisDemux, Hdw, Hdhs, #Hnlb, Hrhs⟩
  ipersist Cprefix'
  ipersist Ccfg
  ipersist Cwatcher
  ipersist Ckv
  ipersist Cdemux
  ipersist Cstore
  ipersist Cready
  ipersist Cstop
  ipersist CinternalCtx
  ipersist CprogressRequestor
  ipersist Cclock
  ipersist cache
  ipersist internalCtx
  obtain ⟨cf, hcf⟩ : ∃ x : CacheFields, x = { cfX with demux := d } := ⟨_, rfl⟩
  have eInv : cacheWgInv (GF := GF) cfX = cacheWgInv cf := by subst hcf; rfl
  have eOpen : cacheOpen (GF := GF) cfX 1 = cacheOpen cf 1 := by subst hcf; rfl
  have eCert : cacheCert (GF := GF) cfX = cacheCert cf := by subst hcf; rfl
  have eRev : R0 = cacheRev (GF := GF) cf := by subst hcf hX; rfl
  have hf : cf.pfx = pfx ∧ cf.cfg = cfg ∧ cf.ready = rd ∧ cf.demux = d ∧ cf.store = st ∧
      cf.γs = γs ∧ cf.scap = sint.nat cfg.HistoryWindowSize' ∧ cf.kv = kv ∧ cf.pr = pr ∧
      cf.watcher = w ∧ cf.ictx = ictx ∧ cf.clock = clk ∧ cf.γwg = γwg ∧ cf.γwb = γwb ∧
      cf.γwr = γwr ∧ cf.γwo = γwo ∧ cf.γwc = γwc ∧ cf.stop = cancel ∧ cf.γop = γop ∧
      cf.γb = γb := by
    subst hcf hX; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hpfx, hcfg, hrd, hd, hst, hγs, hscap, hkv, hpr, hw, hictx, hclk, hγwg, hγwb, hγwr,
    hγwo, hγwc, hstop, hγop, hγb⟩ := hf
  rw [eInv, eOpen, eCert, eRev]
  -- the cache's predicate
  ihave #HisCF : isCacheFields «$r0_ptr» cf γr γd (sint.nat cfg.HistoryWindowSize') $$ []
  · unfold isCacheFields
    rw [hpfx, hcfg, hrd, hd, hst, hγs, hscap, hkv, hpr, hw, hictx, hclk, hγwg, hstop]
    iframe #
    isplitr
    · iexists _
      isplitl []
      · iexact Hictx
      · iexact Hcc
    ipureintro; exact ⟨hP, Hthr⟩
  ihave #HwgInv' : inv cacheWgN (cacheWgInv cf) $$ [HwgInv]
  · iexact HwgInv
  ihave #HisWg' : sync.isWaitGroup (cacheWgAddr «$r0_ptr») cf.γwg cacheWgWGN $$ []
  · rw [hγwg]; iexact HisWg
  -- `cache.waitGroup.Add(2)`
  ihave H2' : ownToks cf.γwb 2 $$ [H2]
  · rw [hγwb]; iexact H2
  ihave Hc2' : ownToks cf.γwc 2 $$ [Hcap2]
  · rw [hγwc]; iexact Hcap2
  wp_apply wp_cacheWg_Add2 «$r0_ptr» cf 1 Hthr $$ [$Hsync $HisWg' $HwgInv' $H2' $Hc2' $Hop]
    as ⟨Hr2, Hop⟩
  icases ownToks_add_1 1 1 cf.γwo $$ Hr2 with ⟨Hr1, Hr1'⟩
  -- the watch loop, with the fresh thread token (its own, for the loop's `Add`s)
  wp_apply wp_fork_tok_body $$ [Hr1 Hdw Hba]
  · iintro Htok
    wp_apply wp_with_defer as %defer defer
    try wp_auto
    wp_apply wp_getWatchLoop «$r0_ptr» cf γr γd (sint.nat cfg.HistoryWindowSize') DemuxCore.init
      $$ [$Hpkg $HisCF Hdw Hba Hr1 Htok] as ⟨Hlr, -⟩
    · unfold cacheWriter cacheWgLoopRunning cacheWgRunningOwed
      rw [hd, hpfx]
      iframe
      isplitr
      · ipureintro
        intro h; exact absurd rfl h
      iexists W64 0
      unfold cacheBound
      rw [hγb]
      iframe
      isplitl
      · iapply etcdReached_zero
      · ipureintro; decide
    iunfold cacheWgLoopRunning at Hlr
    icases Hlr with ⟨Hr1, Htok⟩
    wp_apply wp_cacheWg_DoneOwed «$r0_ptr» cf $$ [$Hsync $HisWg' $HwgInv' $Hr1] as -
    iexact Htok
  -- the progress requestor's loop
  wp_apply wp_fork $$ [Hr1']
  · wp_apply wp_with_defer as %defer defer
    try wp_auto
    wp_apply wp_run pr w clk cfg.ProgressRequestInterval' ictx _
      $$ [$Hpkg $HisPR $HprRun $Hclk $HisPN $Hictx]
    wp_apply wp_cacheWg_DoneOwed «$r0_ptr» cf $$ [$Hsync $HisWg' $HwgInv' Hr1'] as -
    · unfold cacheWgRunningOwed; iexact Hr1'
    itrivial
  -- return the cache with its handles
  try wp_auto
  iapply HΦ
  unfold newCacheResult
  simp only [hvalid, ↓reduceIte]
  isplitr
  · ipureintro; first | rfl | trivial
  iexists cf, γr, γd, γn
  iframe HisCF
  isplitr
  · ipureintro; exact ⟨hpfx, hcfg, hscap⟩
  unfold cacheHandles
  have hM : maxReaders = 2 ^ 30 - 1 := by
    unfold maxReaders; rw [sync.rwmutex.actualMaxReaders_unseal]; rfl
  rw [show (2 ^ 31 - 4 : Nat) = (2 ^ 30 - 1) + (maxReaders - 2) by rw [hM]] at *
  icases ownToks_add_1 (maxReaders - 2) (2 ^ 30 - 1) γwb $$ Hbud with ⟨-, Htoks⟩
  ihave Hts := ownToks_replicate γwb (maxReaders - 2) $$ Htoks
  ihave Hslots := bigSepL_replicate_sep _ _ (maxReaders - 2) $$ [$Hdhs $Hts]
  unfold cacheReader cacheWatchSlot cacheWgSlot
  rw [hst, hγs, hscap, hpfx, hd, hγwb]
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
