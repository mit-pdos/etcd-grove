/-
Proof of `Spec/.../mvcc/store__restore.lean` (the restore plan's R4, option 1: the empty bucket
`NewStore` restores). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__setupMetricsReporter
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewRevBytes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.RevToBytes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadFinishedCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadScheduledCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.restoreIntoIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.restoreChunk
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToRev
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreChunks
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreCut

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

set_option maxHeartbeats 3200000 in
theorem mvcc.store.restore.wp_proof
    (hSetup : mvcc.store.setupMetricsReporter.spec (GF := GF) (hG := hG))
    (hNRB : mvcc.NewRevBytes.spec (GF := GF) (hG := hG))
    (hR2B : mvcc.RevToBytes.spec (GF := GF) (hG := hG))
    (hFin : mvcc.UnsafeReadFinishedCompact.spec (GF := GF) (hG := hG))
    (hSch : mvcc.UnsafeReadScheduledCompact.spec (GF := GF) (hG := hG))
    (hRII : mvcc.restoreIntoIndex.spec (GF := GF) (hG := hG))
    (hRC : mvcc.restoreChunk.spec (GF := GF) (hG := hG))
    (hB2R : mvcc.BytesToRev.spec (GF := GF) (hG := hG))
    (hZI64 : zap.Int64.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    mvcc.store.restore.spec (GF := GF) (hG := hG) := by
  intro s γ b le ti lg q P HF RT WT W Wi Dep NC Cmp PutOk Rb Bt MW SR SRh dqb dqi R RevP0 RevP RevK RevQ
    dqc dql q1 q2 r ents Fin hR hq12 hrec hdq hcut hrcp
  by_cases hR0 : R = []
  rotate_left
  · -- a bucket with data (the restore plan's R5c), thinned at the restored revision (item 18)
    obtain ⟨hRne, ⟨hwf', hlen1, -, hcs⟩, hlease⟩ := hR
    have hb : mvcc.LogB ([[], []] ++ R) := ⟨by omega, hcs⟩
    have hok := mvcc.logEnts_restoreOk ([[], []] ++ R) hb.1 hcs rfl
    have hsub : ents.Sublist (mvcc.logEnts ([[], []] ++ R) 0 ([[], []] ++ R).length) := hcut.1
    have hokE : mvcc.RestoreEntsOk ents := mvcc.restoreOk_sublist hok hsub
    have hRpos : 0 < R.length := List.length_pos_iff.2 hR0
    wp_start as ⟨Hb, #Hbk, Hrt, Hncmp, Hview, Hkvi, Hix, Hig, #Hiw, #Hle, #Hlg, %Hlgnn, Hcur1, Hcmp,
      HRevP0, HFw, HLk, HUl, HK⟩
    iunfold mvcc.restoreViewR at Hview
    simp only [hR0, ↓reduceIte] at *
    icases Hview with ⟨Hbv, Hcr⟩
    wp_auto
    wp_apply (hSetup s b dqb) $$ [$Hb] as Hb
    (try wp_auto)
    wp_apply hNRB as %mn0 ⟨Hmn0, Hmn0c, %Hmn0cap⟩
    wp_apply hNRB as %mx0 ⟨Hmx0, Hmx0c, %Hmx0cap⟩
    (try wp_auto)
    wp_apply (hR2B _ mn0 _ (Or.inl (by simp))) $$ [$Hmn0 $Hmn0c] as %mn ⟨Hmn, Hmnc⟩
    (try wp_auto)
    wp_apply (hR2B _ mx0 _ (Or.inl (by simp))) $$ [$Hmx0 $Hmx0c] as %mx ⟨Hmx, Hmxc⟩
    (try wp_auto)
    wp_apply (wp_map_make1 (K := GoString) (V := w64) go.string
      go_etcd_io.etcd.server.v3.lease.LeaseID.ty) as %ktl Hktl
    (try wp_auto)
    -- `tx := s.b.ReadTx()` over the clean view at the records; `tx.RLock()`
    iunfold mvcc.keyCleanReadR at Hcr
    icases Hcr with ⟨%bi, %Hbi, #HCR⟩
    subst Hbi
    (try wp_auto)
    wp_apply HCR $$ %q %(mvcc.bucketOfEnts ents) [$Hbv $Hrt] as %rt ⟨Hbv, %L, HL, #Hsnap⟩
    iunfold mvcc.keyReadSnapCR at Hsnap
    (try wp_auto)
    wp_apply Hsnap $$ %q [$HL $Hbv] as ⟨Hbv, %Rd, %Tok, Htok, #Hlk⟩
    (try wp_auto)
    -- the compaction keys: the records (the reader's clause under `NC`)
    ihave #Hmc := mvcc.keyReadLockedR_meta _ _ _ _ _ _ _ _ $$ Hlk
    icases Hmc $$ Hncmp with ⟨Hncmp, #Hmeta⟩
    ihave #Hcap := mvcc.keyReadLockedR_cap _ _ _ _ _ _ _ _ _ $$ Hlk
    wp_apply (hFin rt (some r) Rd Tok) $$ [$Htok] as %xf %found ⟨Htok, %Hf⟩
    · iframe #
    obtain ⟨-, -, Hfr⟩ := Hf
    have Hfr := Hfr r rfl
    (try wp_auto)
    ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
    · iPkgInit
    ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
    · iPkgInit
    -- the finished record: `s.compactMainRev = finishedCompact` under `s.revMu` (`revFinW`)
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
        s.[store, go!"compactMainRev"] ↦{dqc} (r.fin.getD (W64 (-1))) ∗ RevP ∗ s_ptr ↦ s ∗
        finishedCompact_ptr ↦ xf))) $$ [Hcmp HRevP0 HFw s finishedCompact]
    · rcases Hfr with ⟨rfl, hfx⟩ | ⟨rfl, hfx, rfl⟩
      · rw [hfx]
        iunfold mvcc.revFinW at HFw
        icases HFw with ⟨%RevK0, HLk0, HUl0⟩
        (try wp_auto)
        wp_apply HLk0 $$ [$HRevP0] as %v0 Hcm2 HRevK0
        icombine Hcmp Hcm2 gives %Hv0
        obtain ⟨-, rfl⟩ := Hv0
        ihave Hcm := ((typedPointsto_dfractional (GF := GF) _ _).dfractional dqc dql).2 $$ [Hcmp Hcm2]
        · iframe
        rw [hdq xf hfx]
        (try wp_auto)
        ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
        · iapply isPkgInit_access $$ Hsch
        icases Hsi with ⟨-, -, -, -, -, -, ⟨%fk, #Hfk, #Hfkb⟩, -⟩
        (try wp_auto)
        wp_apply wp_bytes_to_string _ _ _ $$ Hfkb as -
        (try wp_auto)
        wp_apply hZS _ _ as %f0 -
        (try wp_auto)
        wp_apply hZI64 _ _ as %f1 -
        (try wp_auto)
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply (hInfo lg) $$ []
        · iframe #; ipureintro; exact Hlgnn
        (try wp_auto)
        icases ((typedPointsto_dfractional (GF := GF) _ _).dfractional dqc dql).1 $$
          [Hcm] with ⟨Hcmp, Hcm2⟩
        · rw [hdq xf hfx]; iexact Hcm
        wp_bind (App (Val #(methods (go.GoType.PointerType sync.RWMutex.ty) go!"Unlock"
          #(s.[store, go!"revMu"]))) (Val #()))
        iapply HUl0 $$ Hcm2 HRevK0
        inext
        iintro HRevP
        (try wp_auto)
        iframe
        ipureintro; rfl
      · rw [hfx, Option.getD_none]
        iunfold mvcc.revFinW at HFw
        ihave HRevP := HFw $$ HRevP0
        (try wp_auto)
        iframe
        ipureintro; rfl
    iintro %v ⟨%hv, Hcmp, HRevP, s, finishedCompact⟩
    subst hv
    (try wp_auto)
    wp_apply (hSch rt (some r) Rd Tok) $$ [$Htok] as %xs %sfound ⟨Htok, %Hs⟩
    · iframe #
    obtain ⟨-, -, Hsr⟩ := Hs
    have Hsr := Hsr r rfl
    have hxs : xs = r.sched.getD (W64 0) := by
      rcases Hsr with ⟨-, h⟩ | ⟨-, h, rfl⟩ <;> rw [h] <;> rfl
    subst hxs
    (try wp_auto)
    -- `keysGauge.Set(0)`
    ihave Hinit : (mvccInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hinit with ⟨⟨%e0, #Herr⟩, -, -, ⟨%gg, #Hgauge, -, #Hgset⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HrCK, -⟩
    iunfold gaugeSetSpec at Hgset
    (try wp_auto)
    wp_apply Hgset $$ %(W64 0)
    (try wp_auto)
    -- the read token split: the goroutine reads the keys sent while `restore` goes on ranging
    ihave #Hsp := mvcc.keyReadLockedR_split _ _ _ _ _ _ _ _ $$ Hlk
    iunfold mvcc.rdSplit at Hsp
    icases Hsp $$ Htok with ⟨%TokA, %TokB, HtA, HtB, #HcapA, #HcapB, #HlimA, Hjoin⟩
    -- `rkvc, revc := restoreIntoIndex(s.lg, s.kvindex)` over the image's entries
    wp_apply (hRII lg ti ents Rd TokB e0) $$ [$Hix $HtB] as %rkvc %revc ⟨%γk, %γr, #Hsk, Hprod, #Hsr, Hcons⟩
    · iframe #
      isplitr
      · ipureintro; exact Hlgnn
      ipureintro; exact hokE
    (try wp_auto)
    -- the chunk loop: the entries from `r` on are those not sent yet
    ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hsch
    icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG, -⟩, -⟩
    iunfold mvcc.keyRangeLimSpec at HlimA
    have hmx : mvcc.revBytes (mvcc.revOf ⟨W64 9223372036854775807, W64 9223372036854775807⟩)
        false ++ List.drop 17 (List.replicate 17 (W8 0)) = mvcc.revBytes mvcc.revMax false := by
      simp [mvcc.revOf, mvcc.revMax]
    have hmn : mvcc.revBytes (mvcc.revOf ⟨W64 1, 0⟩) false ++
        List.drop 17 (List.replicate 17 (W8 0)) = mvcc.revBytes ⟨W64 1, W64 0⟩ false := by
      simp [mvcc.revOf]
    rw [hmx] at *
    rw [hmn] at *
    have hE0 : mvcc.entsFromE ents ⟨W64 1, W64 0⟩ = ents := mvcc.entsFromE_one _ hb rfl hsub
    ihave IH : iprop(∃ (rv : mvcc.Rev) (mnS : GoSlice) (sent : List revKeyValue),
        "min" ∷ min_ptr ↦ mnS ∗ "Hmn" ∷ mnS ↦* mvcc.revBytes rv false ∗
        "Hmnc" ∷ ownSliceCap w8 mnS (DFrac.own 1) ∗ "HtA" ∷ TokA ∗
        "Hprod" ∷ spscProducer γk sent ∗ "Hktl" ∷ ktl ↦$ (∅ : GMap GoString w64) ∗
        "%Hr" ∷ ⌜mvcc.entsFromE ents rv = ents.drop sent.length ∧ sent.length ≤ ents.length ∧
          0 ≤ sint.Z rv.main ∧ 0 ≤ sint.Z rv.sub⌝) $$ [min Hmn Hmnc HtA Hprod Hktl]
    · iexists ⟨W64 1, W64 0⟩, mn, []
      iframe
      ipureintro
      refine ⟨by rw [hE0]; rfl, by simp, by word, by word⟩
    have hlz : mvcc.LogNoLease ([[], []] ++ R) := by
      intro cs hcs c hc k v l hcl
      rcases List.mem_append.1 hcs with h | h
      · simp at h; rcases h with rfl | rfl <;> simp at hc
      · exact hlease cs h c hc k v l hcl
    wp_join (iprop(∃ (mnS : GoSlice) (sent : List revKeyValue),
        "min" ∷ min_ptr ↦ mnS ∗ "HtA" ∷ TokA ∗ "Hprod" ∷ spscProducer γk sent ∗
        "%Hall" ∷ ⌜sent.length = ents.length⌝ ∗ "Hktl" ∷ ktl ↦$ (∅ : GMap GoString w64) ∗
        "max" ∷ max_ptr ↦ mx ∗ "keyToLease" ∷ keyToLease_ptr ↦ ktl ∗ "s" ∷ s_ptr ↦ s ∗
        "tx" ∷ tx_ptr ↦ GoInterface.ok rt ∗ "rkvc" ∷ rkvc_ptr ↦ rkvc))
      at (App (App (App (Val doFor) _) _) _) with [IH Hmx max keyToLease s tx rkvc]
      as ⟨%mnS, %sent, min, HtA, Hprod, %Hall, Hktl, max, keyToLease, s, tx, rkvc⟩
    · wp_for IH
      (try wp_auto)
      wp_apply HlimA $$ %bK %mnS %mx %_ %_ %(DFrac.own 1) %(DFrac.own 1) %(W64 10000)
          [$HKeyG $HtA $Hmn $Hmx] as %ks %vs ⟨HtA, Hmn, Hmx, %res, #Hpv, %Hres⟩
      · ipureintro; simp [mvcc.revBytes]
      rw [mvcc.bucketRange_fromE _ hb hsub] at Hres
      have Hres2 := Hres.2 trivial (by decide)
      rw [Hr.1, ← List.map_take] at Hres2
      subst Hres2
      simp only [show (sint.Z (W64 10000)).toNat = 10000 from rfl] at *
      obtain ⟨C, hC⟩ : ∃ C, C = List.take 10000 (List.drop sent.length ents) := ⟨_, rfl⟩
      rw [← hC] at Hres ⊢
      ihave #Hpv' := Hpv
      iunfold mvcc.pairVals at Hpv'
      icases Hpv' with ⟨%kss, %vss, #Hks, #Hvs, %Hlens, #Hels⟩
      ihave %Hkl := ownSlice_len _ _ _ $$ Hks
      have hCl : C.length = sint.nat ks.len := by
        have := Hlens.1; rw [List.length_map] at this; omega
      by_cases hC0 : C = []
      · -- no entry left: every one sent
        have hk0 : ks.len = W64 0 := by rw [hC0] at hCl; simp at hCl; word
        rw [decide_eq_true hk0]
        (try wp_auto)
        wp_for_post
        have Hall : sent.length = ents.length := by
          have hd : List.drop sent.length ents = [] := by
            rcases hd : List.drop sent.length ents with _ | ⟨x, xs⟩
            · rfl
            · rw [hC0, hd] at hC; simp at hC
          have := List.drop_eq_nil_iff.1 hd
          omega
        isplitr
        · ipureintro; rfl
        iexists mnS, sent
        iframe
        ipureintro; exact Hall
      have hkn : ks.len ≠ W64 0 := by
        intro h; rw [h] at hCl; simp at hCl; exact hC0 (List.eq_nil_of_length_eq_zero hCl)
      rw [decide_eq_false hkn]
      (try wp_auto)
      -- `restoreChunk(s.lg, rkvc, keys, vals, keyToLease)`: the chunk's entries sent in order
      have hCsub : ∀ e ∈ C, e ∈ mvcc.logEnts ([[], []] ++ R) 0 ([[], []] ++ R).length := by
        intro e he; rw [hC] at he
        exact hsub.subset (List.mem_of_mem_drop (List.mem_of_mem_take he))
      wp_apply (hRC lg rkvc ktl ks vs C Rd TokA γk (mvcc.rkvProt Rd ents)
          (fun sent => iprop(⌜sent.length = ents.length⌝))
          sent (fun _ _ => iprop(emp))) $$ [$HtA $Hktl $Hprod]
        as ⟨HtA, Hktl, %new, %Hnew, Hprod⟩
      · iframe #
        isplitr
        · ipureintro
          intro e he
          exact mvcc.logEnts_lease _ hlz _ _ e (hCsub e he)
        isplitl []
        · iapply BigSepL.bigSepL_emp.2; itrivial
        iintro !> %j %e %rkv %hj - Hrkv
        iunfold mvcc.rkvProt
        iexists e
        iframe Hrkv
        ipureintro
        constructor
        · rw [hC, List.getElem?_take] at hj
          split at hj
          · rw [List.getElem?_drop] at hj
            rw [show ((sent.length : Int) + (j : Int)).toNat = sent.length + j by omega]
            exact hj
          · cases hj
        · omega
      (try wp_auto)
      have hClen : C.length ≤ 10000 := by rw [hC]; exact List.length_take_le _ _
      by_cases hCs : C.length < 10000
      · -- a short chunk is the last: every entry sent
        have hks : sint.Z ks.len < sint.Z (W64 10000) := by
          have : sint.nat ks.len < 10000 := by omega
          simp only [show sint.Z (W64 10000) = 10000 from rfl]; word
        rw [decide_eq_true hks]
        (try wp_auto)
        wp_for_post
        have Hall : (sent ++ new).length = ents.length := by
          have hCe : C = List.drop sent.length ents := by
            rw [hC]; apply List.take_of_length_le
            rw [hC, List.length_take] at hCs
            omega
          rw [List.length_append, Hnew, hCe, List.length_drop]
          omega
        isplitr
        · ipureintro; rfl
        iexists mnS, sent ++ new
        iframe
        ipureintro; exact Hall
      have hC10 : C.length = 10000 := by omega
      have hks : ¬ sint.Z ks.len < sint.Z (W64 10000) := by
        have : sint.nat ks.len = 10000 := by omega
        simp only [show sint.Z (W64 10000) = 10000 from rfl]; word
      rw [decide_eq_false hks]
      (try wp_auto)
      -- `keys[len(keys)-1][:revBytesLen]`: the chunk's last key, its revision's bytes
      obtain ⟨e, he⟩ : ∃ e, C[9999]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hep : (C.map mvcc.KvEnt.pair)[9999]? = some e.pair := by
        rw [List.getElem?_map, he]; rfl
      icases (BigSepL.bigSepL_lookup_acc hep).1 $$ Hels with ⟨⟨%ksl, %vsl, %Hkv, #HRdk, -⟩, -⟩
      have hkl : sint.nat ks.len = 10000 := by omega
      have hidx : sint.Z (ks.len - W64 1) = 9999 := by word
      rw [if_pos (by rw [hidx]; word)]
      wp_apply (wp_load_slice_index ks (sint.Z (ks.len - W64 1)) kss DFrac.discard ksl (by omega))
        $$ [$Hks]
      · ipureintro; rw [hidx]; exact Hkv.1
      iintro -
      -- the key's bytes, borrowed from the ranging part of the read transaction
      ihave #HcapA' := HcapA
      iunfold mvcc.rdCap at HcapA'
      icases HcapA' $$ %ksl %e.pair.1 HRdk HtA with ⟨%dqk, Hkb, Hkback⟩
      ihave %Hkbl := ownSlice_len _ _ _ $$ Hkb
      ihave %Hkw := ownSlice_wf _ _ _ $$ Hkb
      have heC : e ∈ C := List.mem_of_getElem? he
      have heE := hCsub e heC
      have hel : 17 ≤ e.pair.1.length := by
        show 17 ≤ (mvcc.revBytes e.rev e.tomb).length
        rw [mvcc.revBytes_length]; split <;> omega
      have hcap : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 17) ∧
          sint.Z (W64 17) ≤ sint.Z ksl.cap := by
        simp only [show sint.Z (W64 0) = 0 from rfl, show sint.Z (W64 17) = 17 from rfl]
        have h1 : e.pair.1.length = (sint.Z ksl.len).toNat := Hkbl.1
        have h2 := Hkw.2; have h3 := Hkbl.2; omega
      (try wp_auto)
      simp only [hcap, _root_.and_self, ↓reduceIte]
      icases (ownSlice_slice (W64 0) (W64 17) ksl dqk e.pair.1 (by
          simp only [show sint.Z (W64 0) = 0 from rfl, show sint.Z (W64 17) = 17 from rfl]
          have h1 : e.pair.1.length = (sint.Z ksl.len).toNat := Hkbl.1
          have h3 := Hkbl.2; omega)).1 $$ Hkb with ⟨Hk0, Hk1, Hk2⟩
      have hsub' : subslice (sint.nat (W64 0)) (sint.nat (W64 17)) e.pair.1 =
          mvcc.revBytes e.rev false ++ [] := by
        show subslice 0 17 (mvcc.revBytes e.rev e.tomb) = _
        unfold subslice
        rw [List.drop_zero, List.append_nil]
        cases e.tomb
        · exact List.take_of_length_le (by rw [mvcc.revBytes_false_length]; omega)
        · rw [mvcc.revBytes_true, List.take_append_of_le_length (by rw [mvcc.revBytes_false_length]; omega),
            List.take_of_length_le (by rw [mvcc.revBytes_false_length]; omega)]
      rw [hsub']
      have hbnd := hok.2 e heE
      wp_apply (hB2R (slice.slice ksl w8 (W64 0) (W64 17)) e.rev [] dqk (by simp)
          (by have := hbnd.1; omega) hbnd.2) $$ [$Hk1] as Hk1
      rw [← hsub']
      ihave Hkb := (ownSlice_slice (W64 0) (W64 17) ksl dqk e.pair.1 (by
          simp only [show sint.Z (W64 0) = 0 from rfl, show sint.Z (W64 17) = 17 from rfl]
          have h1 : e.pair.1.length = (sint.Z ksl.len).toNat := Hkbl.1
          have h3 := Hkbl.2; omega)).2 $$ [Hk0 Hk1 Hk2]
      · iframe
      ihave HtA := Hkback $$ Hkb
      (try wp_auto)
      -- `min = RevToBytes(newMin, min)`: the next chunk starts just after the last entry
      wp_apply (hR2B ⟨e.rev.main, e.rev.sub + W64 1⟩ mnS (mvcc.revBytes rv false)
          (Or.inl (mvcc.revBytes_false_length rv))) $$ [$Hmn $Hmnc] as %mnS' ⟨Hmn, Hmnc⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists mvcc.revNext e.rev, mnS', sent ++ new
      have hdrop : (mvcc.revBytes rv false).drop 17 = [] := by
        rw [List.drop_eq_nil_iff, mvcc.revBytes_false_length]; omega
      rw [hdrop, List.append_nil]
      iframe
      have he' : (mvcc.entsFromE ents rv)[10000 - 1]? = some e := by
        rw [Hr.1]
        rw [hC, List.getElem?_take] at he
        simpa using he
      have hnext := mvcc.entsFromE_next ([[], []] ++ R) hb hsub rv 10000 (by omega) e he'
      have hlen2 : sent.length + 10000 ≤ ents.length := by
        rw [hC, List.length_take, List.length_drop] at hC10
        omega
      ipureintro
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hnext, Hr.1, List.drop_drop]
        simp only [List.length_append, Hnew, hC10]
      · simp only [List.length_append, Hnew, hC10] at hlen2 ⊢; exact hlen2
      · show 0 ≤ sint.Z e.rev.main
        have := hbnd.1; omega
      · show 0 ≤ sint.Z (e.rev.sub + W64 1)
        have h1 := hbnd.2
        have h2 : e.rev.sub.toNat < 2 ^ 63 - 1 := by
          obtain ⟨j, i, c, kv, -, -, hj, hgj, -, hc, -, rfl⟩ :=
            mvcc.logEnts_entry ([[], []] ++ R) 0 ([[], []] ++ R).length e heE
          have hil : i < (([[], []] ++ R).getD j []).length := (List.getElem?_eq_some_iff.1 hc).1
          have hb2 := mvcc.getD_len_bound ([[], []] ++ R) hcs j
          show (W64 i).toNat < 2 ^ 63 - 1
          rw [mvcc.w64_toNat_of_lt i (by omega)]; omega
        exact mvcc.sub_succ_nonneg _ h2
    -- `close(rkvc)`: every entry sent
    wp_apply (wp_spsc_close γk rkvc (mvcc.rkvProt Rd ents)
      (fun sent => iprop(⌜sent.length = ents.length⌝)) _) $$ [$Hsk $Hprod]
    · ipureintro; exact Hall
    (try wp_auto)
    -- `s.revMu.Lock()`; `s.currentRev = <-revc`
    iunfold mvcc.revLockW at HLk
    wp_apply HLk $$ [$HRevP] as %v0 Hcur2 HRevK
    icombine Hcur1 Hcur2 gives %Hv0
    obtain ⟨-, rfl⟩ := Hv0
    ihave Hcur := (mvcc.typedPointsto_parts _ _ q1 q2 hq12).2 $$ [Hcur1 Hcur2]
    · iframe
    (try wp_auto)
    wp_apply (wp_spsc_receive γr revc (mvcc.revProt ti TokB ents) (fun _ => iprop(False)) [])
      $$ [$Hsr $Hcons] as %v %okr Hr
    cases okr
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hr with ⟨⟨⟩, -⟩
    simp only [↓reduceIte]
    icases Hr with ⟨Hr, -⟩
    iunfold mvcc.revProt at Hr
    icases Hr with ⟨%Hv, HtB, Hlc, %Lx, Hix, %HL⟩
    obtain ⟨-, Hv⟩ := Hv
    subst Hv
    -- the index's lock at the restored revision's level, made now (`idxRestore_cut`)
    have hwfL : mvcc.LogWf' ([[], []] ++ R) := hwf'.prefix
    have hcrev0 : -1 ≤ r.crev := mvcc.CmpRecs.crev_ge _ r hrec
    have hcrevL : r.crev < ([[], []] ++ R).length :=
      mvcc.recsOk_crev_lt _ r hrec (by simp)
    have Hrep : mvcc.IdxCRepN r.crev (mvcc.evsOf (([[], []] ++ R) ++ [[]])) (mvcc.idxOfEntries Lx) := by
      rw [HL, mvcc.evsOf_append]
      simp only [mvcc.evsOfRev, List.zipIdx_nil, List.map_nil, List.append_nil]
      exact mvcc.idxRestore_cut _ _ _ hwfL hb hcrev0 hcrevL hcut
    imod (mvcc.idx_publishAt (GF := GF) ti γ.idx Lx ([[], []] ++ R) r.crev Hrep hcrev0) $$ Hix Hig Hiw
      with ⟨#Hti, Hrd⟩
    (try wp_auto)
    -- `currentRev` raised to the finished record, then to the scheduled one (`restoreCur_cut`)
    have hfr := mvcc.CmpRecs.finRev_getD r
    have hsr := mvcc.CmpRecs.schedRev_getD r
    wp_join (iprop(∃ c2 : w64, "Hcur" ∷ s.[store, go!"currentRev"] ↦ c2 ∗
        "Hcmp" ∷ s.[store, go!"compactMainRev"] ↦{dqc} (r.fin.getD (W64 (-1))) ∗ "s" ∷ s_ptr ↦ s ∗
        "%Hc2" ∷ ⌜sint.Z c2 = max (sint.Z (mvcc.restoreLastRev ents)) r.finRev⌝))
      with [Hcur Hcmp s] as ⟨%c2, Hcur, Hcmp, s, %Hc2⟩
    · iexists _
      iframe
      ipureintro
      simp only [hfr] at *
      omega
    · iexists _
      iframe
      ipureintro
      simp only [hfr] at *
      omega
    wp_join (iprop(∃ c3 : w64, "Hcur" ∷ s.[store, go!"currentRev"] ↦ c3 ∗ "s" ∷ s_ptr ↦ s ∗
        "scheduledCompact" ∷ scheduledCompact_ptr ↦ r.sched.getD (W64 0) ∗
        "%Hc3" ∷ ⌜sint.Z c3 = max (max (sint.Z (mvcc.restoreLastRev ents)) r.finRev) r.schedRev⌝))
      with [Hcur s scheduledCompact] as ⟨%c3, Hcur, s, scheduledCompact, %Hc3⟩
    · iexists _
      iframe
      ipureintro
      simp only [hsr] at *
      omega
    · iexists _
      iframe
      ipureintro
      simp only [hsr] at *
      omega
    have hc3 : c3 = W64 ((([[], []] ++ R).length : Int) - 1) := by
      rw [mvcc.restoreCur_cut R hRne (List.length_pos_iff.1 hRpos) hb r hrec ents hcut] at Hc3
      have : (([[], []] ++ R).length : Int) < 2 ^ 63 := by have := hb.1; omega
      apply BitVec.eq_of_toNat_eq
      have h1 : sint.Z (W64 ((([[], []] ++ R).length : Int) - 1)) = (([[], []] ++ R).length : Int) - 1 := by
        word
      have h2 := congrArg id Hc3
      word
    subst hc3
    -- `s.revMu.Unlock()`: the lock's part of `currentRev`, the view, the index and the receipts' bound
    iunfold mvcc.revUnlockW at HUl
    wp_bind (App (Val #(methods (go.GoType.PointerType sync.RWMutex.ty) go!"Unlock"
      #(s.[store, go!"revMu"]))) (Val #()))
    icases (mvcc.typedPointsto_parts _ _ q1 q2 hq12).1 $$ Hcur with ⟨Hcur1, Hcur2⟩
    icases persistent_entails_left (receipt_lt _) $$ Hlc with ⟨Hlc, %Hrb⟩
    have Hrb' : mvcc.logCh ([[], []] ++ R) < receiptBound GF := by
      rcases hrcp with h | h
      · rw [h, mvcc.logEnts_length] at Hrb; exact Hrb
      · exact h
    iapply HUl $$ Hcur2 HRevK [Hbv Hrd]
    · iframe Hbv Hrd; iframe Hti; ipureintro; exact Hrb'
    inext
    iintro HRevQ
    (try wp_auto)
    -- `if scheduledCompact <= s.compactMainRev { scheduledCompact = 0 }`: what is resumed
    have hres : r.resumes = true ↔ r.schedRev ≠ 0 ∧ r.finRev < r.schedRev := by
      unfold mvcc.CmpRecs.resumes; simp
    wp_join (iprop("scheduledCompact" ∷ scheduledCompact_ptr ↦
          (if r.resumes then r.sched.getD (W64 0) else W64 0) ∗ "s" ∷ s_ptr ↦ s ∗
        "Hcmp" ∷ s.[store, go!"compactMainRev"] ↦{dqc} (r.fin.getD (W64 (-1)))))
      with [scheduledCompact s Hcmp] as ⟨scheduledCompact, s, Hcmp⟩
    · have hr : r.resumes = false := by
        cases h : r.resumes
        · rfl
        · exfalso
          obtain ⟨-, hlt⟩ := hres.1 h
          rw [← hfr, ← hsr] at hlt
          omega
      rw [hr]
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
    · cases h : r.resumes
      · have hz : r.schedRev = 0 := by
          apply Classical.byContradiction
          intro hne
          have hlt : r.finRev < r.schedRev := by rw [← hfr, ← hsr]; omega
          rw [hres.2 ⟨hne, hlt⟩] at h; cases h
        have h0 : r.sched.getD (W64 0) = W64 0 := by
          rw [← hsr] at hz; apply BitVec.eq_of_toNat_eq; word
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [h0]
        iframe
      · simp only [↓reduceIte]
        iframe
    -- `for key, lid := range keyToLease`: the map is empty
    (try wp_func_lits)
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (_ : List GoString) (_ : Int) => iprop(True)) $$ Hktl
    iintro %keys -
    isplitr
    · ipureintro; trivial
    isplitr
    · imodintro
      iintro %i %key %v ⟨-, %Hkv⟩
      simp at Hkv
    iintro - Hktl
    (try wp_auto)
    -- `tx.RUnlock()`, the two parts of the read token joined
    ihave Htok := Hjoin $$ HtA HtB
    ihave #Hru := mvcc.keyReadLockedR_unlock _ _ _ _ _ _ _ _ _ $$ Hlk
    wp_bind (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #()))
    iapply Hru $$ [Htok]
    · iexact Htok
    inext
    iintro Hrt
    (try wp_auto)
    -- `s.lg.Info("kvstore restored", zap.Int64("current-rev", s.currentRev))`
    wp_apply hZI64 _ _ as %f1 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply (hInfo lg) $$ []
    · iframe #; ipureintro; exact Hlgnn
    (try wp_auto)
    -- what `restore` has now; the resumed compaction, if any (`resumeK`)
    ihave HD : mvcc.restoreDone s (GoInterface.ok bi) ti q1 dqb dqi dqc ([[], []] ++ R) ents r RT NC RevQ
        $$ [Hrt Hncmp Hlc HRevQ Hcur1 Hcmp Hb Hkvi]
    · iunfold mvcc.restoreDone
      iframe
    iunfold mvcc.resumeK at HK
    cases hres' : r.resumes
    · simp only [hres', Bool.false_eq_true, ↓reduceIte] at *
      (try wp_auto)
      iapply HΦ
      iapply HK $$ HD
    simp only [hres', ↓reduceIte] at *
    have hsc : r.sched.getD (W64 0) ≠ W64 0 := by
      intro h
      have := (hres.1 hres').1
      rw [← hsr, h] at this
      exact this rfl
    rw [decide_eq_false hsc]
    (try wp_auto)
    wp_apply HK $$ [$HD] as %ch %err HFin
    (try wp_auto)
    cases err with
    | nil =>
      -- `s.lg.Info("resume scheduled compaction", ...)`
      (try wp_auto)
      wp_apply hZI64 _ _ as %g1 -
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [g1]
      isplitr
      · ipureintro; rfl
      iintro %gsl ⟨-, -⟩
      (try wp_auto)
      wp_apply (hInfo lg) $$ []
      · iframe #; ipureintro; exact Hlgnn
      (try wp_auto)
      iapply HΦ
      iexact HFin
    | ok ei =>
      -- `s.lg.Warn("compaction encountered error", ...)`
      (try wp_auto)
      wp_apply hZI64 _ _ as %g1 -
      (try wp_auto)
      wp_apply hZE _ as %g2 -
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [g1, g2]
      isplitr
      · ipureintro; rfl
      iintro %gsl ⟨-, -⟩
      (try wp_auto)
      wp_apply (hWarn lg) $$ []
      · iframe #; ipureintro; exact Hlgnn
      (try wp_auto)
      iapply HΦ
      iexact HFin
  -- the empty bucket (`NewStore`): no record, no entry
  subst hR0
  have hents : ents = [] := by
    have h := hcut.1
    have h2 : mvcc.logEnts ([[], []] ++ ([] : mvcc.Log)) 0 ([[], []] ++ ([] : mvcc.Log)).length = [] :=
      mvcc.logEnts_two
    rw [h2] at h
    exact List.sublist_nil.1 h
  subst hents
  wp_start as ⟨Hb, #Hbk, Hrt, Hncmp, Hview, Hkvi, Hix, Hig, #Hiw, #Hle, #Hlg, %Hlgnn, Hcur1, Hcmp,
    HRevP0, HFw, HLk, HUl, HK⟩
  iunfold mvcc.restoreViewR at Hview
  simp only [↓reduceIte]
  icases Hview with ⟨Hbv, %Hmr⟩
  obtain ⟨-, rfl⟩ := Hmr
  rw [mvcc.isKeyBackendGR_empty, mvcc.CmpRecs.crev_empty]
  iunfold mvcc.revFinW at HFw
  simp only [mvcc.CmpRecs.empty]
  ihave HRevP := HFw $$ HRevP0
  wp_auto
  wp_apply (hSetup s b dqb) $$ [$Hb] as Hb
  (try wp_auto)
  -- `min, max := NewRevBytes(), NewRevBytes()`, then their revisions' bytes
  wp_apply hNRB as %mn0 ⟨Hmn0, Hmn0c, %Hmn0cap⟩
  wp_apply hNRB as %mx0 ⟨Hmx0, Hmx0c, %Hmx0cap⟩
  (try wp_auto)
  wp_apply (hR2B _ mn0 _ (Or.inl (by simp))) $$ [$Hmn0 $Hmn0c] as %mn ⟨Hmn, Hmnc⟩
  (try wp_auto)
  wp_apply (hR2B _ mx0 _ (Or.inl (by simp))) $$ [$Hmx0 $Hmx0c] as %mx ⟨Hmx, Hmxc⟩
  (try wp_auto)
  -- `keyToLease := make(map[string]lease.LeaseID)`
  wp_apply (wp_map_make1 (K := GoString) (V := w64) go.string
    go_etcd_io.etcd.server.v3.lease.LeaseID.ty) as %ktl Hktl
  (try wp_auto)
  -- `tx := s.b.ReadTx()`; `tx.RLock()`
  iunfold mvcc.isKeyBackendG at Hbk
  icases Hbk with ⟨%bi, %Hbi, -, #HRTx, -, -, -⟩
  subst Hbi
  (try wp_auto)
  wp_apply HRTx $$ %q %(∅ : mvcc.Bucket) [$Hbv $Hrt] as %rt ⟨Hbv, %L, HL, #Hsnap⟩
  iunfold mvcc.keyReadSnap at Hsnap
  (try wp_auto)
  wp_apply Hsnap $$ %q [$HL $Hbv] as ⟨Hbv, %m', %Rd, %Tok, Htok, #Hlk, #Hthin⟩
  (try wp_auto)
  -- the compaction keys: neither is there (the reader's clause under `NC`, at no record)
  ihave #Hmc := mvcc.keyReadLocked_meta _ _ _ _ _ _ _ $$ Hlk
  icases Hmc $$ Hncmp with ⟨Hncmp, #Hmeta⟩
  ihave #Hcap := mvcc.keyReadLocked_cap _ _ _ _ _ _ _ _ $$ Hlk
  wp_apply (hFin rt (some mvcc.CmpRecs.empty) Rd Tok) $$ [$Htok] as %xf %found ⟨Htok, %Hf⟩
  · rw [mvcc.metaReadSpecR_empty]; iframe #
  obtain ⟨-, Hf0, Hfnf⟩ := Hf
  have Hfound : found = false := by
    rcases Hfnf _ rfl with ⟨-, h⟩ | ⟨h, -⟩
    · cases h
    · exact h
  subst Hfound
  have Hxf := Hf0 rfl
  subst Hxf
  (try wp_auto)
  wp_apply (hSch rt (some mvcc.CmpRecs.empty) Rd Tok) $$ [$Htok] as %xs %sfound ⟨Htok, %Hs⟩
  · rw [mvcc.metaReadSpecR_empty]; iframe #
  obtain ⟨-, Hs0, Hsnf⟩ := Hs
  have Hsfound : sfound = false := by
    rcases Hsnf _ rfl with ⟨-, h⟩ | ⟨h, -⟩
    · cases h
    · exact h
  subst Hsfound
  have Hxs := Hs0 rfl
  subst Hxs
  (try wp_auto)
  -- `keysGauge.Set(0)`
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨⟨%e0, #Herr⟩, -, -, ⟨%gg, #Hgauge, -, #Hgset⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HrCK, -⟩
  iunfold gaugeSetSpec at Hgset
  (try wp_auto)
  wp_apply Hgset $$ %(W64 0)
  (try wp_auto)
  -- `rkvc, revc := restoreIntoIndex(s.lg, s.kvindex)`: no entry to send (the bucket is empty);
  -- the goroutine reads nothing (`Rd` false)
  ihave #Hrc0 : mvcc.rdCap (GF := GF) (fun _ _ => iprop(False)) iprop(True) $$ []
  · iunfold mvcc.rdCap
    iintro !> %s0 %b0 HF -
    iexfalso; iexact HF
  wp_apply (hRII lg ti [] (fun _ _ => iprop(False)) iprop(True) e0) $$ [$Hix]
    as %rkvc %revc ⟨%γk, %γr, #Hsk, Hprod, #Hsr, Hcons⟩
  · iframe #
    isplitr
    · ipureintro; exact Hlgnn
    ipureintro
    exact ⟨List.Pairwise.nil, fun e h => by cases h⟩
  (try wp_auto)
  -- the chunk loop: the first range read finds nothing (the bucket is empty), so it ends
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG, -⟩, -⟩
  ihave #Hlim := mvcc.keyReadLocked_rangeLim _ _ _ _ _ _ $$ Hlk
  iunfold mvcc.keyRangeLimSpec at Hlim
  -- the snapshot read is the empty bucket's (a thinning of it)
  iunfold mvcc.snapThin at Hthin
  icases Hthin with ⟨%Hthin', -⟩
  have Hm' : m' = ∅ := by
    apply (GMap.lookup_empty_iff m').1
    intro k
    cases h : m'.lookup k with
    | none => rfl
    | some v => have := Hthin' k v h; simp at this
  subst Hm'
  have Hbr : ∀ klo khi, mvcc.bucketRange (∅ : mvcc.Bucket) klo khi = [] := by
    intro klo khi; simp [mvcc.bucketRange]
  wp_for
  (try rw [if_pos (by simp)])
  (try wp_auto)
  wp_apply Hlim $$ %bK %mn %mx %_ %_ %(DFrac.own 1) %(DFrac.own 1) %(W64 10000)
      [$HKeyG $Htok $Hmn $Hmx] as %ks %vs ⟨Htok, Hmn, Hmx, %res, #Hpv, %Hres⟩
  · ipureintro; simp [mvcc.revBytes]
  rw [Hbr] at Hres
  have Hres0 : res = [] := List.sublist_nil.1 Hres.1
  subst Hres0
  iunfold mvcc.pairVals at Hpv
  icases Hpv with ⟨%kss, %vss, #Hks, #Hvs, %Hlens, -⟩
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  have Hk0 : ks.len = W64 0 := by
    have h1 := Hkl.1; have h2 := Hlens.1
    simp only [List.length_nil] at h2
    rw [h2] at h1; unfold sint.nat at h1; word
  (try wp_auto)
  rw [decide_eq_true Hk0]
  (try wp_auto)
  wp_for_post
  -- `close(rkvc)`: every entry (none) sent
  wp_apply (wp_spsc_close γk rkvc (mvcc.rkvProt (fun _ _ => iprop(False)) [])
    (fun sent => iprop(⌜sent.length = ([] : List mvcc.KvEnt).length⌝)) []) $$ [$Hsk $Hprod]
  · ipureintro; rfl
  (try wp_auto)
  -- `s.revMu.Lock()`; `s.currentRev = <-revc`
  iunfold mvcc.revLockW at HLk
  wp_apply HLk $$ [$HRevP] as %v0 Hcur2 HRevK
  icombine Hcur1 Hcur2 gives %Hv0
  obtain ⟨-, rfl⟩ := Hv0
  ihave Hcur := (mvcc.typedPointsto_parts _ _ q1 q2 hq12).2 $$ [Hcur1 Hcur2]
  · iframe
  (try wp_auto)
  wp_apply (wp_spsc_receive γr revc (mvcc.revProt ti iprop(True) []) (fun _ => iprop(False)) [])
    $$ [$Hsr $Hcons] as %v %okr Hr
  cases okr
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hr with ⟨⟨⟩, -⟩
  simp only [↓reduceIte]
  icases Hr with ⟨Hr, -⟩
  iunfold mvcc.revProt at Hr
  icases Hr with ⟨%Hv, -, Hlc, %L, Hix, %HL⟩
  obtain ⟨-, Hv⟩ := Hv
  subst Hv
  have HL0 : L = [] := by
    have : mvcc.idxOfEntries L = [] := HL
    unfold mvcc.idxOfEntries at this
    exact List.map_eq_nil_iff.1 this
  subst HL0
  have Hrep : mvcc.IdxCRepN (-1) (mvcc.evsOf (([[], []] ++ []) ++ [[]])) (mvcc.idxOfEntries []) :=
    mvcc.IdxCRepN_of (mvcc.IdxCRep.nil (by decide))
  imod (mvcc.idx_publishAt (GF := GF) ti γ.idx [] ([[], []] ++ []) (-1) Hrep (by decide)) $$ Hix Hig Hiw
    with ⟨#Hti, Hrd⟩
  (try wp_auto)
  iunfold mvcc.revUnlockW at HUl
  rw [show mvcc.restoreLastRev [] = W64 ((([[], []] ++ ([] : mvcc.Log)).length : Int) - 1) from rfl]
  wp_bind (App (Val #(methods (go.GoType.PointerType sync.RWMutex.ty) go!"Unlock"
    #(s.[store, go!"revMu"]))) (Val #()))
  icases (mvcc.typedPointsto_parts _ _ q1 q2 hq12).1 $$ Hcur with ⟨Hcur1, Hcur2⟩
  iapply HUl $$ Hcur2 HRevK [Hbv Hrd]
  · iframe Hbv Hrd; iframe Hti; ipureintro
    exact receiptBound_pos (GF := GF)
  inext
  iintro HRevQ
  (try wp_auto)
  -- `for key, lid := range keyToLease`: the map is empty
  (try wp_func_lits)
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List GoString) (_ : Int) => iprop(True)) $$ Hktl
  iintro %keys -
  isplitr
  · ipureintro; trivial
  isplitr
  · imodintro
    iintro %i %key %v ⟨-, %Hkv⟩
    simp at Hkv
  iintro - Hktl
  (try wp_auto)
  -- `tx.RUnlock()`
  iunfold mvcc.keyReadLocked at Hlk
  icases Hlk with ⟨#Hru, -⟩
  wp_bind (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #()))
  iapply Hru $$ [Htok]
  · iexact Htok
  inext
  iintro Hrt
  (try wp_auto)
  -- `s.lg.Info("kvstore restored", zap.Int64("current-rev", s.currentRev))`
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_apply hZI64 _ _ as %f1 -
  (try wp_auto)
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply (hInfo lg) $$ []
  · iframe #; ipureintro; exact Hlgnn
  (try wp_auto)
  -- nothing resumed: `restore` has what it ends with
  iunfold mvcc.resumeK at HK
  simp only [show (⟨none, none⟩ : mvcc.CmpRecs).resumes = false from rfl, Bool.false_eq_true,
    ↓reduceIte]
  iapply HΦ
  iapply HK
  iunfold mvcc.restoreDone
  simp only [mvcc.CmpRecs.empty, Option.getD_none]
  iframe

end proof

end EtcdGrove
end Perennial
