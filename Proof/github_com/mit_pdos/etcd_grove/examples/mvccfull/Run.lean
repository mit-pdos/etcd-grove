/- Lean-first (no Rocq counterpart). The proof of `Run`: proved (`RunLemmas.lean`: the allocations,
the shares lent and gathered, `memEnd`).

The outline: `normalize`; `walkKeys` (`keysOf`, sorted, not empty); `zap.NewNop`; the history
(`hist0`, its names); the runner's fields persisted (`writerCtx`: `rnCtx`, `runnerCfg`, the weights,
the counters' invariants, `rdShared`, `0 ≤ Ops < 2 ^ 38` from `runCfgOk`); `memberPath`, `newMember` twice (the files `filePathsM`'s
first two); `startEpoch` of each (the members' shares split, `lentOk`); `startReaders`; `write`;
`stopReaders`; `hashing(cfg.Mix.Read)`, false under `runCfgOk`'s `readMixOk`
(`hashingM_of_readMixOk`), so `x.hashes()` is skipped; for each member `endEpoch`,
`inc_retire`, `shut`, `open`, `checkAll`, `inc_retire`, `shut`; the counters' `Load`s.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.normalize
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.walkKeys
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.memberPath
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__newMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__startEpoch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__startReaders
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__write
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__stopReaders
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.hashing
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__endEpoch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__shut
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__open
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkAll
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.RunLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.newHistory

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 3200000 in
theorem Run.wp_proof
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (wp_normalize : normalize.spec (GF := GF) (hG := hG))
    (wp_walkKeys : walkKeys.spec (GF := GF) (hG := hG))
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_memberPath : memberPath.spec (GF := GF) (hG := hG))
    (wp_newMember : runner.newMember.spec (GF := GF) (hG := hG))
    (wp_startEpoch : runner.startEpoch.spec (GF := GF) (hG := hG))
    (wp_startReaders : runner.startReaders.spec (GF := GF) (hG := hG))
    (wp_write : runner.write.spec (GF := GF) (hG := hG))
    (wp_stopReaders : runner.stopReaders.spec (GF := GF) (hG := hG))
    (wp_hashing : hashing.spec (GF := GF) (hG := hG))
    (wp_endEpoch : runner.endEpoch.spec (GF := GF) (hG := hG))
    (wp_shut : runner.shut.spec (GF := GF) (hG := hG))
    (wp_open : runner.open.spec (GF := GF) (hG := hG))
    (wp_checkAll : runner.checkAll.spec (GF := GF) (hG := hG)) :
    Run.spec (GF := GF) (hG := hG) := by
  intro cfg wr _ _ hcfg hck hdbo hdbc
  haveI : ∀ N l, Persistent (ctrInv (GF := GF) N l) := by intro N l; unfold ctrInv; infer_instance
  haveI := isInc_persistent hpers
  haveI := hpers.1
  haveI : ∀ x a b, Persistent (runnerMs (GF := GF) x a b) := by
    intro x a b; unfold runnerMs; infer_instance
  haveI : ∀ x ks cfg h γh, Persistent (rnCtx (GF := GF) x ks cfg h γh) := by
    intro x ks cfg h γh; unfold rnCtx runnerKeys runnerH ctrInv; infer_instance
  haveI : ∀ x ks, Persistent (runnerKeys (GF := GF) x ks) := by
    intro x ks; unfold runnerKeys; infer_instance
  haveI : ∀ x h, Persistent (runnerH (GF := GF) x h) := by intro x h; unfold runnerH; infer_instance
  haveI : ∀ x cfg wr, Persistent (runnerCfg (GF := GF) x cfg wr) := by
    intro x cfg wr; unfold runnerCfg runnerRangeMix; infer_instance
  haveI : ∀ x, Persistent (rdShared (GF := GF) x) := by intro x; unfold rdShared ctrInv; infer_instance
  wp_start as ⟨Hmix, Hfiles, Htok, #Hvoff⟩
  wp_auto
  wp_apply wp_normalize
  (try wp_auto)
  have hdep : (if sint.Z cfg.Depth' < 1 then W64 1 else cfg.Depth') = (normalizeM cfg).Depth' := rfl
  have hdep1 : 1 ≤ sint.Z (normalizeM cfg).Depth' := by
    unfold normalizeM; dsimp only; split
    · decide
    · omega
  rw [hdep]
  wp_apply (wp_walkKeys slice.nil [] [] (normalizeM cfg).Depth' (by simp; omega)) $$ []
    as %ksl ⟨Hksl, Hkscap⟩
  · iframe #
    isplitl
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  (try wp_auto)
  wp_apply (mvccrand.wp_slice_literal_ex (V := GoMap))
  wp_apply (wp_map_make1 (K := GoString) (V := kvRec)) as %m1 Hm1
  wp_apply (wp_map_make1 (K := GoString) (V := kvRec)) as %m2 Hm2
  iexists [m1, m2]
  isplitr
  · ipureintro; rfl
  iintro %ssl ⟨Hss, Hssc⟩
  wp_auto
  wp_apply (wp_slice_literal (V := GoSlice) [slice.nil, slice.nil])
  isplitr
  · ipureintro; rfl
  iintro %csl ⟨Hcs, Hcsc⟩
  wp_auto
  -- the history: its cells, its ghost state, its lock with the run's reader slots
  irename «$v3» => Hh
  generalize «$v3_ptr» = h at *
  iStructNamedSuffix Hh "H"
  iclear _H
  generalize (slice.mk ssl (W64 (go.arrayLiteralSize
      [KeyedElement none (ElementLiteralValue []), KeyedElement none (ElementLiteralValue [])]))
      (W64 (go.arrayLiteralSize
        [KeyedElement none (ElementLiteralValue []), KeyedElement none (ElementLiteralValue [])]))) = sS
  generalize (slice.mk csl (W64 (go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.untypedNil UntypedNil),
        KeyedElement none (ElementExpression go.untypedNil UntypedNil)]))
      (W64 (go.arrayLiteralSize
        [KeyedElement none (ElementExpression go.untypedNil UntypedNil),
          KeyedElement none (ElementExpression go.untypedNil UntypedNil)]))) = sC
  imod ownMap_persist $$ Hm1 with #Hm1
  imod ownMap_persist $$ Hm2 with #Hm2
  imod ownSlice_persist $$ Hss with #Hss
  imod ownSlice_persist $$ Hcs with #Hcs
  ihave #Hnil : (slice.nil ↦*□ ([] : List change) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave #Hnilw : (slice.nil ↦*□ ([] : List w64) : IProp GF) $$ []
  · iapply ownSlice_nil
  let hx : HistCells := ⟨sS, sC, slice.nil, [m1, m2], [slice.nil, slice.nil], [], hist0⟩
  imod ghostVar_alloc (GF := GF) hx with ⟨%γg, Hg⟩
  icases ghostVar_split γg hx (1 : Qp).half (1 : Qp).half $$ [Hg] with ⟨Hg1, Hg2⟩
  · rw [Qp.half_add_half]; iexact Hg
  imod mono_list_own_alloc (GF := GF) hist0 with ⟨%γl, Hl, -⟩
  ihave ⟨Hl1, Hl2⟩ : monoListAuthOwn (GF := GF) γl (1 : Qp).half hist0 ∗
      monoListAuthOwn (GF := GF) γl (1 : Qp).half hist0 $$ [Hl]
  · iapply ((monoListAuthOwn_fractional (GF := GF) γl hist0).fractional (1 : Qp).half (1 : Qp).half).1
    rw [Qp.half_add_half]; iexact Hl
  ihave #Hlb0 := monoListLbOwn_get γl _ hist0 $$ Hl2
  let γh : HistNames := ⟨γg, γl⟩
  ihave HhR : histR h γh 1 $$ [statesH changesH compsH Hg1 Hl1]
  · iunfold histR
    iexists hx
    iframe
    iunfold histElems
    iunfold statesP
    iunfold changesP
    simp only [hist0, hx, List.zip_cons_cons, List.zip_nil_right, List.length_cons, List.length_nil]
    simp
    iframe #
  ihave HhW : histW γh hist0 [] $$ [Hg2 Hl2 Hssc Hcsc]
  · iunfold histW
    iexists hx
    iframe
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iapply ownSliceCap_nil
  -- the configuration, normalized, and its facts
  obtain ⟨hmixN, hops0, hopsB, hthr, hlimN, hcblN, hkl⟩ := hcfg
  have hks := keysOf_bounds (sint.nat (normalizeM cfg).Depth')
  rw [show sint.nat (if sint.Z cfg.Depth' < 1 then W64 1 else cfg.Depth') - ([] : GoString).length =
    sint.nat (normalizeM cfg).Depth' from by simp only [List.length_nil, Nat.sub_zero]; rfl,
    List.nil_append]
  rw [show filePathsM cfg = filePathsM (normalizeM cfg) from rfl,
    show cfg.Mix' = (normalizeM cfg).Mix' from rfl]
  have hopsN : 0 ≤ sint.Z (normalizeM cfg).Ops' ∧ sint.Z (normalizeM cfg).Ops' < 2 ^ 38 :=
    ⟨hops0, hopsB⟩
  have hthrN : 2 * max 0 (sint.Z (normalizeM cfg).Readers') +
      4 * max 0 (sint.Z (normalizeM cfg).Streams') + 3 ≤ 2 ^ 28 := hthr
  have hlimN' : sint.Z (limOf (normalizeM cfg)) ≤ 2 ^ 57 := hlimN
  have hcblN' : batchLimitOk (cblOf (normalizeM cfg)) := hcblN
  clear hlimN hcblN hthr hops0 hopsB
  rw [show walkM [] (sint.nat (normalizeM cfg).Depth') = keysOf (sint.nat (normalizeM cfg).Depth')
    from rfl]
  have hsorted := keysOf_sorted (sint.nat (normalizeM cfg).Depth')
  have hkne := keysOf_ne (sint.nat (normalizeM cfg).Depth') (by
    have : sint.nat (normalizeM cfg).Depth' = (sint.Z (normalizeM cfg).Depth').toNat := rfl
    omega)
  have hknn := keysOf_ne_nil (sint.nat (normalizeM cfg).Depth')
  generalize keysOf (sint.nat (normalizeM cfg).Depth') = ks at *
  generalize hN : normalizeM cfg = cfgN at *
  have hPfx : cfg.Prefix' = cfgN.Prefix' := by rw [← hN]; rfl
  have hksn : ∀ k ∈ ks, (k.length : Int) < 2 ^ 63 - 1 := by
    intro k hk; have := hks.2 k hk; have := hks.1; omega
  -- the history's lock, with a reader slot for the writer, `n` for the readers, `ns` per member for
  -- its streams' receivers
  let nR := 2 * (sint.Z cfgN.Readers').toNat
  let ns := (sint.Z cfgN.Streams').toNat
  imod hist_allocF h γh (1 + nR + ns + ns) (by
      rw [sync.rwmutex.actualMaxReaders_unseal]
      simp only [nR, ns]; omega) $$ [muH HhR] with ⟨#Hhist, Hrds⟩
  · iframe
  icases (histRds_add h γh (1 + nR + ns) ns).1 $$ Hrds with ⟨Hrds, Hrds1⟩
  icases (histRds_add h γh (1 + nR) ns).1 $$ Hrds with ⟨Hrds, Hrds0⟩
  icases (histRds_add h γh 1 nR).1 $$ Hrds with ⟨Hrd, HrdsR⟩
  icases (histRds_one h γh).1 $$ Hrd with Hrd
  -- the runner's fields
  irename «$r0» => Hx
  generalize «$r0_ptr» = x at *
  iStructNamedSuffix Hx "R"
  iclear _R
  try simp only []
  ipersist cfgR
  ipersist keysR
  ipersist lgR
  ipersist hR
  imod ownSlice_persist $$ Hksl with #Hksl
  imod ctrInv_alloc (readersN .@ "stop") _ $$ readStopR with #Cstop
  imod ctrInv_alloc (readersN .@ "reads") _ $$ readsR with #Creads
  imod ctrInv_alloc (readersN .@ "revisions") _ $$ revisionsR with #Crev
  imod ctrInv_alloc (readersN .@ "compactions") _ $$ compactionsR with #Ccmp
  imod ctrInv_alloc (readersN .@ "restores") _ $$ restoresR with #Cres
  imod ctrInv_alloc (readersN .@ "restarts") _ $$ restartsR with #Crst
  imod ctrInv_alloc (sCtrN .@ "events") _ $$ eventsR with #Cev
  imod ctrInv_alloc (sCtrN .@ "progress") _ $$ progressR with #Cpr
  imod ctrInv_alloc (sCtrN .@ "compacted") _ $$ compactedR with #Ccd
  imod ctrInv_alloc (sCtrN .@ "cancels") _ $$ cancelsR with #Ccn
  imod ctrInv_alloc (sCtrN .@ "hashPairs") _ $$ hashPairsR with #Chp
  -- the readers' wait group
  have hTB : threadBound GF ≤ 2 ^ 31 := ThreadBoundLe.le_of (2 ^ 28) (by omega)
  imod sync.init_WaitGroup (rdWgN.@"wg") _ $$ readWgR with ⟨%γwg, #Hwg, Hwctr, Hwwait⟩
  ihave #Hlaw := sync.tokJoin.lendLaw_false (GF := GF) rdWgN
  imod sync.tokJoin.init rdWgN iprop(False) _ γwg ⊤ hTB $$ [Hwctr Hwwait] with Hadd
  · iframe #; iframe
  -- the weights, read-only from now on
  iunfold mixOwn at Hmix
  icases Hmix with ⟨%dq, %ws, %wo, %wc, %wrr, %wa, %wst, Hws, Hwo, Hwc, Hwrr, Hwr, Hwa, Hwst⟩
  imod ownSlice_persist $$ Hws with #Hws
  imod ownSlice_persist $$ Hwo with #Hwo
  imod ownSlice_persist $$ Hwc with #Hwc
  imod ownSlice_persist $$ Hwrr with #Hwrr
  imod ownSlice_persist $$ Hwr with #Hwr
  imod ownSlice_persist $$ Hwa with #Hwa
  imod ownSlice_persist $$ Hwst with #Hwst
  ihave #Hctx : writerCtx x ks cfgN wr h γh $$ []
  · iunfold writerCtx
    iunfold rnCtx
    iunfold runnerKeys
    iunfold runnerH
    iunfold runnerCfg
    iunfold runnerRangeMix
    iunfold rdShared
    iunfold ctrInv
    iunfold ctrInv at Cstop Creads Crev Ccmp Cres Crst Cev Cpr Ccd Ccn
    iframe #
    isplitl
    · isplitl
      · iPkgInit
      ipureintro; exact ⟨⟨hsorted, hkne⟩, hknn⟩
    isplitr
    · ipureintro; exact hmixN
    isplitl
    · iPkgInit
    isplitl
    · iPkgInit
    isplitl
    · iPkgInit
    isplitl
    · iPkgInit
    ipureintro; exact ⟨hksn, hopsN.1, hopsN.2, hkl⟩
  -- the members' files
  rw [show filePathsM cfgN = memberPathM cfgN.Prefix' 0 :: memberPathM cfgN.Prefix' 1 ::
    (List.range' 1 (sint.nat cfgN.Ops')).map (buildPathM cfgN.Prefix') from rfl]
  icases BigSepL.bigSepL_cons.1 $$ Hfiles with ⟨Hf0, Hfiles⟩
  icases BigSepL.bigSepL_cons.1 $$ Hfiles with ⟨Hf1, Hfiles⟩
  -- the members
  (try wp_auto)
  try rw [hPfx]
  wp_apply (wp_memberPath _ (W64 0) (by decide))
  wp_apply (wp_newMember x ks cfgN wr h γh (W64 0) (memberPathM cfgN.Prefix' 0)
      (by decide) (by decide) hdbo hck hlimN' hcblN') $$ [Htok Hrd Hf0]
    as %mp0 ⟨Htok, Hrd, %m0, %f0, %v0, %k0, %Hv0, Hm0, Hst0, #Hreg0⟩
  · iframe #; iframe
  (try wp_auto)
  wp_apply wp_slice_literal (V := Loc) [mp0]
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  (try wp_auto)
  ihave Hms0 : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hmsc0 := ownSliceCap_nil (GF := GF) (V := Loc)
  wp_apply wp_slice_append $$ [$Hms0 $Hmsc0 $Hsl2] as %msl ⟨Hmsl, Hmscap, -⟩
  iclear Hmsc0
  (try wp_auto)
  try rw [hPfx]
  wp_apply (wp_memberPath _ (W64 1) (by decide))
  wp_apply (wp_newMember x ks cfgN wr h γh (W64 1) (memberPathM cfgN.Prefix' 1)
      (by decide) (by decide) hdbo hck hlimN' hcblN') $$ [Htok Hrd Hf1]
    as %mp1 ⟨Htok, Hrd, %m1', %f1, %v1, %k1, %Hv1, Hm1', Hst1, #Hreg1⟩
  · iframe #; iframe
  (try wp_auto)
  wp_apply wp_slice_literal (V := Loc) [mp1]
  isplitr
  · ipureintro; rfl
  iintro %sl3 ⟨Hsl3, -⟩
  (try wp_auto)
  wp_apply wp_slice_append $$ [$Hmsl $Hmscap $Hsl3] as %msl' ⟨Hmsl, Hmscap, -⟩
  (try wp_auto)
  rw [show ([] ++ [mp0] ++ [mp1] : List Loc) = [mp0, mp1] from rfl]
  ihave %Hmslen := ownSlice_len $$ Hmsl
  ipersist msR
  imod ownSlice_persist $$ Hmsl with #Hmsl
  ihave #Hms : runnerMs x mp0 mp1 $$ []
  · iunfold runnerMs; iexists msl'; iframe #
  have hmslen : sint.Z msl'.len = 2 := by
    have h1 := Hmslen.1; have : sint.nat msl'.len = (sint.Z msl'.len).toNat := rfl
    simp only [List.length_cons, List.length_nil] at h1
    have := Hmslen.2; omega
  -- the shares lent to the epoch's readers and streams
  ispecialize Hm0 $$ %([] : List OpM)
  ispecialize Hm1' $$ %([] : List OpM)
  let u := runShare ns
  let nw := mvccReaderN - nR - 2 * ns
  have hnw : nw + nR + 2 * ns = mvccReaderN ∧ 1 ≤ nw := by
    have h1 : mvccReaderN = backend.rdStockN - 7 := mvccReaderN_eq
    have h2 := backend.rdStockN_val
    simp only [nw, nR, ns]
    omega
  icases memW_lend hpers hRdSplit ks γh [] 0 mp0 m0 f0 v0 k0 x h cfgN u u u nw nR ns
    (runShare_sum ns) hnw.1 $$ [Hm0 Hrds0] with ⟨Hm0, Hlent0, Htoks0⟩
  · iframe
  icases memW_lend hpers hRdSplit ks γh [] 1 mp1 m1' f1 v1 k1 x h cfgN u u u nw nR ns
    (runShare_sum ns) hnw.1 $$ [Hm1' Hrds1] with ⟨Hm1', Hlent1, Htoks1⟩
  · iframe
  icases memW_isInc hpers ks γh [] 0 mp0 m0 f0 v0 u nw k0 $$ Hm0 with ⟨Hm0, #Hisinc0⟩
  icases memW_isInc hpers ks γh [] 1 mp1 m1' f1 v1 u nw k1 $$ Hm1' with ⟨Hm1', #Hisinc1⟩
  icases memW_kv ks γh [] 0 mp0 m0 f0 v0 u nw k0 $$ Hm0 with ⟨Hkv0, Hm0⟩
  icases memW_kv ks γh [] 1 mp1 m1' f1 v1 u nw k1 $$ Hm1' with ⟨Hkv1, Hm1'⟩
  ihave #Hrn : rnCtx x ks cfgN h γh $$ []
  · iunfold writerCtx at Hctx; icases Hctx with ⟨#H, -⟩; iexact H
  let E0 : Ep := ⟨x, h, ks, γh, cfgN, 0, mp0, m0, v0.ι, v0.kv⟩
  let E1 : Ep := ⟨x, h, ks, γh, cfgN, 1, mp1, m1', v1.ι, v1.kv⟩
  -- `for _, m := range x.ms { x.startEpoch(m) }`
  ihave HI : (∃ (j : w64) (mv : Loc), "i" ∷ i_ptr ↦ j ∗ "m" ∷ m_ptr ↦ mv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 2⌝ ∗
      "H0" ∷ (if sint.Z j = 0 then
          mF go!"kv" mp0 ↦{DFrac.own u} v0.kv ∗ mF go!"streams" mp0 ↦ (slice.nil : GoSlice) ∗
            ([∗list] _x ∈ List.replicate ns (), epochTok E0 u)
        else mF go!"kv" mp0 ↦{DFrac.own u} v0.kv ∗
          ∃ (sl : GoSlice) (ss : List Loc), mF go!"streams" mp0 ↦ sl ∗ sl ↦* ss ∗
            ownSliceCap Loc sl (DFrac.own 1) ∗ ⌜ss.length = ns⌝ ∗ [∗list] s ∈ ss, epochStream E0 u s) ∗
      "H1" ∷ (if sint.Z j ≤ 1 then
          mF go!"kv" mp1 ↦{DFrac.own u} v1.kv ∗ mF go!"streams" mp1 ↦ (slice.nil : GoSlice) ∗
            ([∗list] _x ∈ List.replicate ns (), epochTok E1 u)
        else mF go!"kv" mp1 ↦{DFrac.own u} v1.kv ∗
          ∃ (sl : GoSlice) (ss : List Loc), mF go!"streams" mp1 ↦ sl ∗ sl ↦* ss ∗
            ownSliceCap Loc sl (DFrac.own 1) ∗ ⌜ss.length = ns⌝ ∗ [∗list] s ∈ ss, epochStream E1 u s)
      : IProp GF) $$ [i m Hkv0 Hst0 Htoks0 Hkv1 Hst1 Htoks1]
  · iexists W64 0, _
    iframe
    simp only [show sint.Z (W64 0) = 0 from rfl, ↓reduceIte, show (0 : Int) ≤ 1 from by decide]
    isplitr
    · ipureintro; decide
    simp only [named]
    iframe
  wp_for HI
  by_cases Hlt : sint.Z j < sint.Z msl'.len
  · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    (try wp_auto)
    rw [hmslen] at Hlt
    rcases (show sint.Z j = 0 ∨ sint.Z j = 1 by omega) with hj | hj
    · have hj' : j = W64 0 := by word
      subst hj'
      have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z msl'.len := by rw [hmslen]; decide
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index msl' (sint.Z (W64 0)) [mp0, mp1] DFrac.discard mp0 (by decide)
        $$ [Hmsl] as -
      · iframe #; ipureintro; rfl
      (try wp_auto)
      simp only [show sint.Z (W64 0) = 0 from rfl, ↓reduceIte, show (0 : Int) ≤ 1 from by decide]
      icases H0 with ⟨Hk, Hs, Ht⟩
      wp_apply (wp_startEpoch E0 u u) $$ [Hk Hs Ht] as ⟨Hk, %sl, %ss, Hs, Hsl, Hcap, %Hssl, Hes⟩
      · iunfold epCtx; iframe #; iframe
      (try wp_auto)
      wp_for_post
      iframe
      iexists W64 0 + W64 1, mp0
      simp only [named, show sint.Z (W64 0 + W64 1) = 1 from rfl, show ((1 : Int) = 0) = False from by decide,
        ↓reduceIte, show (1 : Int) ≤ 1 from by decide]
      isplitl [i]
      · iexact i
      isplitl [m]
      · iexact m
      isplitr
      · ipureintro; decide
      isplitl [Hk Hs Hsl Hcap Hes]
      · iframe
        ipureintro; exact Hssl
      iframe
    · have hj' : j = W64 1 := by word
      subst hj'
      have hb : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z msl'.len := by rw [hmslen]; decide
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index msl' (sint.Z (W64 1)) [mp0, mp1] DFrac.discard mp1 (by decide)
        $$ [Hmsl] as -
      · iframe #; ipureintro; rfl
      (try wp_auto)
      simp only [show sint.Z (W64 1) = 1 from rfl, show ((1 : Int) = 0) = False from by decide,
        ↓reduceIte, show (1 : Int) ≤ 1 from by decide]
      icases H1 with ⟨Hk, Hs, Ht⟩
      wp_apply (wp_startEpoch E1 u u) $$ [Hk Hs Ht] as ⟨Hk, %sl, %ss, Hs, Hsl, Hcap, %Hssl, Hes⟩
      · iunfold epCtx; iframe #; iframe
      (try wp_auto)
      wp_for_post
      iframe
      iexists W64 1 + W64 1, mp1
      simp only [named, show sint.Z (W64 1 + W64 1) = 2 from rfl, show ((2 : Int) = 0) = False from by decide,
        show ((2 : Int) ≤ 1) = False from by decide, ↓reduceIte]
      isplitl [i]
      · iexact i
      isplitl [m]
      · iexact m
      isplitr
      · ipureintro; decide
      isplitl [H0]
      · iexact H0
      iframe
      ipureintro; exact Hssl
  rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
  have hj2 : sint.Z j = 2 := by omega
  simp only [hj2, show ((2 : Int) = 0) = False from by decide,
    show ((2 : Int) ≤ 1) = False from by decide, ↓reduceIte]
  icases H0 with ⟨Hkv0, %sl0, %ss0, Hst0, Hsl0, Hcap0, %Hssl0, Hes0⟩
  icases H1 with ⟨Hkv1, %sl1, %ss1, Hst1, Hsl1, Hcap1, %Hssl1, Hes1⟩
  ihave Hm0 := Hm0 $$ Hkv0
  ihave Hm1' := Hm1' $$ Hkv1
  (try wp_auto)
  -- `x.startReaders()`
  let γ : FullNames := ⟨γh, m0, m1'⟩
  ihave #HctxR : runnerKeys x ks ∗ runnerH x h ∗ runnerCfg x cfgN wr ∗ rdShared x $$ []
  · iunfold writerCtx at Hctx
    icases Hctx with ⟨#Hrn', #Hcfg', -, #Hrds', -⟩
    iunfold rnCtx at Hrn'
    icases Hrn' with ⟨-, -, #Hk', -, #Hh', -⟩
    iframe #
  icases HctxR with ⟨#HrK, #HrH, #HrC, #HrS⟩
  wp_apply (wp_startReaders x cfgN wr ks h γ mp0 mp1 (v0.ι, v0.kv) (v1.ι, v1.kv) u hmixN)
    $$ [Htok Hadd HrdsR Hlent0 Hlent1] as ⟨Htok, Hadd⟩
  · iframe #
    iunfold rdStock
    iframe
    done
  (try wp_auto)
  -- `x.write()`
  have hH0 : histAt ks ([] : List OpM) 0 = hist0 := by simp only [histAt, runM_zero]; rfl
  have hC0 : compsAt ks ([] : List OpM) 0 = [] := by simp only [compsAt, runM_zero]; rfl
  have hG0 : grantedAfter ks ([] : List OpM) 0 = [] := by simp only [grantedAfter, runM_zero]; rfl
  obtain ⟨hv0o, hv0p, hk0⟩ := Hv0
  obtain ⟨hv1o, hv1p, hk1⟩ := Hv1
  ihave Hw : writerOwn x ks cfgN h γ mp0 mp1 f0 f1 [] v0 v1 0 0 u u $$
      [logR nextLeaseR valsR buildsR HhW Hrd Hfiles Hm0 Hm1' Hst0 Hsl0 Hcap0 Hes0 Hst1 Hsl1 Hcap1 Hes1
        Hadd]
  · iunfold writerOwn
    dsimp only
    iframe #
    iframe Hadd
    isplitl [logR]
    · iunfold logOwn
      iexists slice.nil, []
      iframe
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      isplitr
      · ipureintro; exact ⟨rfl, fun i o h => by simp at h⟩
      simp only [List.zip_nil_left]
      iapply BigSepL.bigSepL_nil.2; itrivial
    isplitl [nextLeaseR valsR buildsR]
    · iunfold writerCtrs
      iexists W64 0
      iframe
      ipureintro
      simp only [List.length_nil, hG0]
      exact ⟨by decide, fun _ h => by simp at h, by decide⟩
    isplitl [HhW]
    · simp only [List.length_nil, hH0, hC0]; iexact HhW
    iframe Hrd
    isplitr
    · ipureintro
      simp only [List.length_nil]
      refine ⟨hv0o, by omega, by omega⟩
    isplitr
    · ipureintro; omega
    isplitl [Hfiles]
    · rw [Nat.sub_zero]
      rw [BigSepL.bigSepL_map]
      iexact Hfiles
    isplitl [Hm0]
    · iexists u, nw, k0
      iframe
      ipureintro
      refine ⟨⟨runShare_sum ns, hnw.1⟩, hnw.2, ?_⟩
      have : sint.nat cfgN.Ops' = (sint.Z cfgN.Ops').toNat := rfl
      omega
    isplitl [Hm1']
    · iexists u, nw, k1
      iframe
      ipureintro
      refine ⟨⟨runShare_sum ns, hnw.1⟩, hnw.2, ?_⟩
      have : sint.nat cfgN.Ops' = (sint.Z cfgN.Ops').toNat := rfl
      omega
    isplitl [Hst0 Hsl0 Hcap0 Hes0]
    · iexists sl0, ss0; iframe; ipureintro; exact Hssl0
    · iexists sl1, ss1; iframe; ipureintro; exact Hssl1
  wp_apply (wp_write x ks cfgN wr h γ mp0 mp1 f0 f1 [] v0 v1 0 0 u u (by omega) hdbo hdbc hck hlimN'
      hcblN') $$ [Htok Hw] as ⟨Htok, %ops, %v0', %v1', %nv', %nb', %q', %qs', %Hops, Hw⟩
  · iframe #; iframe
  (try wp_auto)
  -- `x.stopReaders()`
  iunfold writerOwn at Hw
  icases Hw with ⟨-, -, -, Hlog, Hctrs, HhW, Hrd, %Hops', %Hnb, Hfiles,
    ⟨%qw0, %nw0, %k0', Hm0, %Hl0⟩, ⟨%qw1, %nw1, %k1', Hm1, %Hl1⟩, Hss0, Hss1, Hadd⟩
  wp_apply (lc := 1) (wp_stopReaders x nR
      (rdStock h γ mp0 mp1 (v0'.ι, v0'.kv) (v1'.ι, v1'.kv) nR q')) $$ [Hadd] as ⟨-, Hstock⟩
  · iframe #; iframe
  imod lc_fupd_elim_later $$ Hlc1 Hstock with Hstock
  iunfold rdStock at Hstock
  icases Hstock with ⟨HrdsR, Hlent0, Hlent1⟩
  (try wp_auto)
  -- `hashing(x.cfg.Mix.Read)`: false under F1's scope
  ihave #Hcf := typedPointsto_split _ _ _ $$ cfgR
  simp only [TypedPointsto.typedPointstoDef]
  iNamedSuffix Hcf "C"
  ihave #Hmf := typedPointsto_split _ _ _ $$ MixC
  simp only [TypedPointsto.typedPointstoDef]
  iNamedSuffix Hmf "C"
  (try wp_auto)
  wp_apply (wp_hashing cfgN.Mix'.Read' wr DFrac.discard) $$ [] as %b ⟨-, %Hb⟩
  · iframe #
  rw [hashingM_of_readMixOk hmixN] at Hb
  subst Hb
  (try wp_auto)
  -- the final loop: for each member, `endEpoch`, `shut`, `open`, `checkAll`, `shut`
  iunfold logOwn at Hlog
  icases Hlog with ⟨%lsl, %lps, -, -, -, %Hlogp, -⟩
  have hlogOk := Hlogp.2
  have hlen : ops.length < 2 ^ 38 := by have := Hops'.2.2; omega
  icases histW_lb γ.h _ _ $$ HhW with ⟨-, #Hlb⟩
  obtain ⟨⟨hq0, hn0⟩, hnw0, -⟩ := Hl0
  obtain ⟨⟨hq1, hn1⟩, hnw1, -⟩ := Hl1
  ihave HE0 : memEnd x h ks γ.h cfgN ops q' qs' nR 0 mp0 γ.m0 f0 v0' $$ [Hm0 Hss0 Hlent0]
  · iunfold memEnd
    iexists qw0, nw0, k0'
    iframe #; iframe
    ipureintro; exact ⟨hq0, hn0, hnw0, Hops'.1⟩
  ihave HE1 : memEnd x h ks γ.h cfgN ops q' qs' nR 1 mp1 γ.m1 f1 v1' $$ [Hm1 Hss1 Hlent1]
  · iunfold memEnd
    iexists qw1, nw1, k1'
    iframe #; iframe
    ipureintro; exact ⟨hq1, hn1, hnw1, Hops.2.2⟩
  ihave HJ : (∃ (j : w64) (mv : Loc), "i" ∷ i_ptr ↦ j ∗ "m" ∷ m_ptr ↦ mv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 2⌝ ∗ "Htok" ∷ threadTok ∗ "Hrd" ∷ histRd h γ.h ∗
      "H0" ∷ (if sint.Z j ≤ 0 then memEnd x h ks γ.h cfgN ops q' qs' nR 0 mp0 γ.m0 f0 v0'
        else iprop(True)) ∗
      "H1" ∷ (if sint.Z j ≤ 1 then memEnd x h ks γ.h cfgN ops q' qs' nR 1 mp1 γ.m1 f1 v1'
        else iprop(True)) : IProp GF) $$ [i m Htok Hrd HE0 HE1]
  · iexists W64 0, _
    simp only [named, show sint.Z (W64 0) = 0 from rfl, show (0 : Int) ≤ 0 from by decide,
      show (0 : Int) ≤ 1 from by decide, ↓reduceIte]
    isplitl [i]
    · iexact i
    isplitl [m]
    · iexact m
    isplitr
    · ipureintro; decide
    iframe
  wp_for HJ
  by_cases Hlt : sint.Z j < sint.Z msl'.len
  · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    (try wp_auto)
    rw [hmslen] at Hlt
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z msl'.len := ⟨Hj.1, by omega⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    -- the member of this iteration
    ihave Hcur : (∃ (ii : Nat) (mp : Loc) (mm : MemberNames) (f : GoFunc) (v : MemS),
        ⌜ii = sint.nat j ∧ [mp0, mp1][sint.nat j]? = some mp⌝ ∗
        memEnd x h ks γ.h cfgN ops q' qs' nR ii mp mm f v ∗
        (if sint.Z (j + W64 1) ≤ 0 then memEnd x h ks γ.h cfgN ops q' qs' nR 0 mp0 γ.m0 f0 v0'
          else iprop(True)) ∗
        (if sint.Z (j + W64 1) ≤ 1 then memEnd x h ks γ.h cfgN ops q' qs' nR 1 mp1 γ.m1 f1 v1'
          else iprop(True)) : IProp GF) $$ [H0 H1]
    · rcases (show sint.Z j = 0 ∨ sint.Z j = 1 by omega) with hj | hj
      · have hj' : j = W64 0 := by word
        subst hj'
        simp only [show sint.Z (W64 0) = 0 from rfl, show sint.Z (W64 0 + W64 1) = 1 from rfl,
          show (0 : Int) ≤ 0 from by decide, show (0 : Int) ≤ 1 from by decide,
          show ((1 : Int) ≤ 0) = False from by decide, show (1 : Int) ≤ 1 from by decide, ↓reduceIte]
        iexists 0, mp0, γ.m0, f0, v0'
        iframe
        ipureintro; exact ⟨rfl, rfl⟩
      · have hj' : j = W64 1 := by word
        subst hj'
        simp only [show sint.Z (W64 1) = 1 from rfl, show sint.Z (W64 1 + W64 1) = 2 from rfl,
          show ((1 : Int) ≤ 0) = False from by decide, show (1 : Int) ≤ 1 from by decide,
          show ((2 : Int) ≤ 0) = False from by decide, show ((2 : Int) ≤ 1) = False from by decide,
          ↓reduceIte]
        iexists 1, mp1, γ.m1, f1, v1'
        iframe
        ipureintro; exact ⟨rfl, rfl⟩
    icases Hcur with ⟨%ii, %mp, %mm, %f, %v, %Hcur, Htodo, H0, H1⟩
    obtain ⟨hii, hmp⟩ := Hcur
    wp_apply wp_load_slice_index msl' (sint.Z j) [mp0, mp1] DFrac.discard mp Hj.1 $$ [Hmsl] as -
    · iframe #; ipureintro; exact hmp
    (try wp_auto)
    iunfold memEnd at Htodo
    icases Htodo with ⟨%qw, %nw, %k, Hm, %Hl, ⟨%sl, %ss, Hst, Hsl, Hcap, %Hssl, Hes⟩, Hlent, #Hreg⟩
    obtain ⟨hq, hn, hnw, hvops⟩ := Hl
    iunfold memW at Hm
    icases Hm with ⟨-, -, Hc⟩
    iunfold memCore at Hc
    icases Hc with ⟨#Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hleases, %Hvops,
      Hinc, Hopen, Hback, HhookIs, Hrdrs, Hbk, Hles, %HU⟩
    iunfold incW at Hinc
    icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
    have hR1 : mvccReaders (GF := GF) v.ι.kv nw ⊣⊢
        mvccReaders v.ι.kv (nw - 1) ∗ mvccReaders v.ι.kv 1 := by
      have := hRdSplit v.ι.kv (nw - 1) 1; rwa [Nat.sub_add_cancel hnw] at this
    icases hR1.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
    have hrv : revAfter ks ops v.ops < (histAt ks ops ops.length).length := by
      rw [hvops]; unfold revAfter MSt.rev histAt; have := runM_hs_len ks ops ops.length; omega
    have hrvZ : sint.Z (W64 (revAfter ks ops v.ops : Int)) = revAfter ks ops v.ops := by
      have : revAfter ks ops v.ops < 2 ^ 63 := by
        have := runM_hs_len ks ops v.ops; unfold revAfter MSt.rev; omega
      word
    -- `x.endEpoch(m)`
    wp_apply (wp_endEpoch ⟨x, h, ks, γ.h, cfgN, ii, mp, mm, v.ι, v.kv⟩ qs' qw sl ss
        (W64 (revAfter ks ops v.ops : Int)) (histAt ks ops ops.length)
        (by rw [hrvZ]; omega) (by rw [hrvZ]; exact_mod_cast hrv)
        (by rw [hrvZ]; have := runM_hs_len ks ops v.ops; unfold revAfter MSt.rev; omega))
      $$ [Hst Hsl Hes Hrev Hrd Hr1 Hret] as ⟨Hst, Hrev, Hrd, Hr1, Hlive, Htoks⟩
    · iunfold epCtx; dsimp only [epLive]; iunfold incLive; iframe #; iframe
    (try wp_auto)
    dsimp only [epLive]
    iunfold incLive at Hlive
    icases Hlive with ⟨-, Hret⟩
    ihave Hsh : incShare mp v.ι v.kv qw nw $$ [Hret Hkv Hrdrs Hr1]
    · iunfold incShare; iframe; iapply hR1.2; iframe
    rw [Hssl]
    icases shares_join hpers hRdSplit ⟨x, h, ks, γ.h, cfgN, ii, mp, mm, v.ι, v.kv⟩ qw q' qs' nw _ _
      hq hn $$ [Hsh Hlent Htoks] with ⟨Hsh, -⟩
    · iframe
    iunfold incShare at Hsh
    icases Hsh with ⟨Hret, Hkv, Hrdrs⟩
    imod inc_retire hpers ks γ.h ii mp mm v.ι v.kv $$ [Hret] with Hms
    · iframe #; iframe
    icases (memberState_split ks γ.h mp mm v.ι.kv).1 $$ Hms with ⟨%σ', %b', %Hl', Hσ, Hcarry⟩
    iunfold memberCarry at Hcarry
    icases Hcarry with ⟨Hσc, Hc1, Hc2, Hc3, Hc4, Hbc, Hc5, Hc6, Hc7, Hc8, %Hcp⟩
    icombine Hσw Hσc gives %Hσeq
    icombine Hbw Hbc gives %Hbeq
    obtain ⟨-, rfl⟩ := Hσeq
    obtain ⟨-, rfl⟩ := Hbeq
    iunfold lessorW at Hles
    icases Hles with ⟨%rd, %r, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Hrb, %Hrecs, Hstop, -⟩
    iunfold bkKeep at Hbk
    icases Hbk with ⟨%HbkP, #Hbk1, #Hbk2, Hbk3, Hbk4, Hbk5, Hbk6, Hbk7⟩
    ihave #Hmv : isMvcc v.kv v.ι.kv $$ []
    · iunfold isInc at Hisinc; icases Hisinc with ⟨-, #H, -⟩; iexact H
    -- `x.shut(m)`
    wp_apply (wp_shut x ks cfgN wr h γ.h mp v.path v.bk v.lp v.kv v.ι.kv (σOf ks ops v.ops)
        (leasesAfter ks ops v.ops) r k hdbc rfl Hrecs)
      $$ [Hkv Hle Hbe Hopen Hrdrs Hback Hσ Hbk3 Hbk4 Hbk5 Hbk6 Hbk7 Hstop Hrb]
      as ⟨Hkv, Hle, Hbe, %D, %u, Hfile, Himg, %HrecD⟩
    · iframe #; iframe; iunfold bkKeep; iframe #; iframe; ipureintro; exact HbkP
    (try wp_auto)
    -- `x.open(m)`
    wp_apply (wp_open x ks cfgN wr h γ.h ops ii mp mm f v.ops v.path D u v.b Hl'
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #v.bk.be) (lease.lessorIface v.lp) v.kv hlogOk Hvops hlen hdbo hck hlimN' hcblN')
      $$ [Htok Hrd Hpath Hbe Hle Hkv Hrev Hcmp Hleases Hfile Himg HhookOk Hσc Hc1 Hc2 Hc3 Hc4 Hbc
        Hc5 Hc6 Hc7 Hc8 Hσw Hbw]
      as ⟨Htok, Hrd, %v', %k', %Hv', Hc'⟩
    · iframe #; iframe
      isplitr
      · rw [hvops]; iexact Hlb
      isplitr
      · ipureintro; rw [HbkP.1] at HrecD; exact HrecD
      iunfold memberCarry; iframe; ipureintro; exact Hcp
    (try wp_auto)
    obtain ⟨hv'ops, hv'path, hv'b, hk'⟩ := Hv'
    -- `x.checkAll(m)`
    have hRN : 1 ≤ mvccReaderN := by
      rw [mvccReaderN_eq, backend.rdStockN_val]; decide
    wp_apply (wp_checkAll x ks cfgN wr h γ.h ops ii mp mm f v' 1 mvccReaderN k' hlogOk hRN hlen)
      $$ [Hrd Hc'] as ⟨Hrd, Hc'⟩
    · iframe #; iframe; rw [hv'ops, hvops]; iexact Hlb
    (try wp_auto)
    -- `x.shut(m)` again, the reopened incarnation retired
    iunfold memCore at Hc'
    icases Hc' with ⟨-, -, -, -, Hbe', Hle', Hkv', -, -, -, %Hvops',
      Hinc', Hopen', Hback', -, Hrdrs', Hbk', Hles', -⟩
    iunfold incW at Hinc'
    icases Hinc' with ⟨#Hisinc', Hret', Hσw', Hbw'⟩
    imod inc_retire hpers ks γ.h ii mp mm v'.ι v'.kv $$ [Hret'] with Hms'
    · iframe #; iframe
    icases (memberState_split ks γ.h mp mm v'.ι.kv).1 $$ Hms' with ⟨%σ'', %b'', %Hl'', Hσ', Hcarry'⟩
    iunfold memberCarry at Hcarry'
    icases Hcarry' with ⟨Hσc', -, -, -, -, -, -, -, -, -, -⟩
    icombine Hσw' Hσc' gives %Hσeq'
    obtain ⟨-, rfl⟩ := Hσeq'
    iunfold lessorW at Hles'
    icases Hles' with ⟨%rd', %r', -, -, -, -, -, -, -, -, -, -, -, -, -, -, Hrb', %Hrecs', Hstop', -⟩
    iunfold bkKeep at Hbk'
    icases Hbk' with ⟨%HbkP', #Hbk1', #Hbk2', Hbk3', Hbk4', Hbk5', Hbk6', Hbk7'⟩
    ihave #Hmv' : isMvcc v'.kv v'.ι.kv $$ []
    · iunfold isInc at Hisinc'; icases Hisinc' with ⟨-, #H, -⟩; iexact H
    wp_apply (wp_shut x ks cfgN wr h γ.h mp v'.path v'.bk v'.lp v'.kv v'.ι.kv (σOf ks ops v'.ops)
        (leasesAfter ks ops v'.ops) r' k' hdbc rfl Hrecs')
      $$ [Hkv' Hle' Hbe' Hopen' Hrdrs' Hback' Hσ' Hbk3' Hbk4' Hbk5' Hbk6' Hbk7' Hstop' Hrb']
      as -
    · iframe #; iframe; iunfold bkKeep; iframe #; iframe; ipureintro; exact HbkP'
    (try wp_auto)
    wp_for_post
    simp only [named]
    iframe
    ipureintro
    have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
    omega
  rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
  (try wp_auto)
  -- the report: the counters' `Load`s
  wp_apply (ctrInv_load (readersN .@ "revisions") _ _) as %c0
  · iexact Crev
  (try wp_auto)
  wp_apply (ctrInv_load (sCtrN .@ "events") _ _) as %c1
  · iexact Cev
  (try wp_auto)
  wp_apply (ctrInv_load (sCtrN .@ "progress") _ _) as %c2
  · iexact Cpr
  (try wp_auto)
  wp_apply (ctrInv_load (sCtrN .@ "compacted") _ _) as %c3
  · iexact Ccd
  (try wp_auto)
  wp_apply (ctrInv_load (sCtrN .@ "cancels") _ _) as %c4
  · iexact Ccn
  (try wp_auto)
  wp_apply (ctrInv_load (readersN .@ "reads") _ _) as %c5
  · iexact Creads
  (try wp_auto)
  wp_apply (ctrInv_load (sCtrN .@ "hashPairs") _ _) as %c6
  · iexact Chp
  (try wp_auto)
  wp_apply (ctrInv_load (readersN .@ "compactions") _ _) as %c7
  · iexact Ccmp
  (try wp_auto)
  wp_apply (ctrInv_load (readersN .@ "restores") _ _) as %c8
  · iexact Cres
  (try wp_auto)
  wp_apply (ctrInv_load (readersN .@ "restarts") _ _) as %c9
  · iexact Crst
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end mvccfull
end EtcdGrove
end Perennial
