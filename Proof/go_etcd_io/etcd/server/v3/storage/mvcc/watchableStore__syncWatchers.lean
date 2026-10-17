/-
Proof of `Spec/.../mvcc/watchableStore__syncWatchers.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__syncWatchers
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__size
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__choose
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.cohortsByRevision
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__syncWatcherCohort
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.SyncModel
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.SyncWatchersLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]


set_option maxRecDepth 20000 in
theorem mvcc.watchableStore.syncWatchers.wp_proof
    (hSize : mvcc.watcherGroup.size.spec (GF := GF) (hG := hG))
    (hChoose : mvcc.watcherGroup.choose.spec (GF := GF) (hG := hG))
    (hCoh : mvcc.cohortsByRevision.spec (GF := GF) (hG := hG))
    (hSWC : mvcc.watchableStore.syncWatcherCohort.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.syncWatchers.spec (GF := GF) (hG := hG) := by
  intro s st γ
  wp_start as ⟨#Hws, HR⟩
  ihave #HwsAll : mvcc.isWatchableStore s st γ $$ []
  · iexact Hws
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HmaxB, -, ⟨%gS, #HgS, #HgSS⟩,
    ⟨%gP, #HgP, #HgPS⟩, -, #HmaxW, -, ⟨%gS', #HgS', #HgSet⟩, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold mvcc.watchReader at HR
  icases HR with ⟨Hsr0, Hmur⟩
  iunfold mvcc.storeReader at Hsr0
  iNamedSuffix Hsr0 "R"
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.watchStoreInv s γ 1)) $$ Hlc1 HP with HP
  iunfold mvcc.watchStoreInv at HP
  icases HP with ⟨%σ, HP⟩
  iunfold mvcc.watchStoreBody at HP
  iNamed HP
  icases mvcc.watchBudget_bound _ _ _ $$ Hwt with ⟨Hwt, %HMb⟩
  icombine HgS HgS' gives %HgEq
  wp_apply (hSize (mvcc.unsyncedAddr s) σ.Wu 1) $$ [$Hunsynced] as ⟨Hunsynced, %HszWu⟩
  wp_if_destruct
  · -- no unsynced watcher
    ihave HP : mvcc.watchStoreBody s γ 1 σ $$ [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo
        Hmeta Hwt Hmem]
    · iunfold mvcc.watchStoreBody; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hvlen, Hok⟩
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl HP]
    · inext; iunfold mvcc.watchStoreInv; iexists σ; iexact HP
    (try wp_auto)
    iapply HΦ
    iunfold mvcc.watchReader
    iframe Hmur
    iunfold mvcc.storeReader
    iexists ti
    simp only [named]
    iframe
    iframe #
  ihave #Hs0 : mvcc.isStore st γ.st $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamedSuffix Hs "S"
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HrevMuR] as ⟨Hrl, HQ⟩
  wp_auto_lc 2
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv st γ.st sync.rfrac)) $$ Hlc1 HQ with HQ
  iunfold mvcc.revMuInv at HQ
  icases HQ with ⟨%C, %ntok, %cQ, HQ⟩
  iNamedSuffix HQ "Q"
  imod mvcc.crevFrozen_agree γ.st _ cQ HcQ.1 $$ HfrzR HcrevQ with ⟨HcrevQ, %HcQ1⟩
  subst HcQ1
  icases persistent_entails_right (mvcc.idxLogAuth_cert_prefix _ _ _ _) $$ [$HlogQ $Hcert]
    with ⟨%HpC, HlogQ, -⟩
  wp_auto
  -- the unsynced members' states, for `choose`
  icases persistent_entails_right (mvcc.sw_unsynced_bounds γ σ Hok _ C) $$ [$Hmem $HlogQ]
    with ⟨%Hbd, Hmem, HlogQ⟩
  have hCne : 1 ≤ C.length := List.length_pos_iff.2 HneQ
  have hClt : C.length < 2 ^ 63 := by
    have := HbudgetQ; omega
  icases (mvcc.sw_bigSepM_split (fun k _ => (σ.Wu !! k).isSome) σ.ST _).1 $$ Hst with ⟨Hstu, Hstr⟩
  have hSTu : ∀ k, (Iris.Std.PartialMap.filter (fun k _ => (σ.Wu !! k).isSome) σ.ST : GMap Loc mvcc.WatcherSt) !! k =
      if (σ.Wu !! k).isSome then σ.ST !! k else none := by
    intro k; rw [mvcc.sw_filter_lookup]; cases σ.ST !! k <;> cases (σ.Wu !! k).isSome <;> rfl
  generalize hSTuD : (Iris.Std.PartialMap.filter (fun k _ => (σ.Wu !! k).isSome) σ.ST : GMap Loc mvcc.WatcherSt) = STu at hSTu ⊢
  have hcur : sint.Z (W64 ((C.length : Int) - 1)) = (C.length : Int) - 1 := by word
  wp_apply (hChoose (mvcc.unsyncedAddr s) σ.Wu STu (W64 512) (W64 ((C.length : Int) - 1)) (W64 (-1)))
    $$ [$Hunsynced Hstu] as %g %minRev ⟨Hstu, Hch⟩
  · iunfold mvcc.ownStates; iframe Hstu
    ipureintro
    refine ⟨⟨fun w hw => ?_, fun w st hw => ?_⟩, by have := Hok.wu_size; omega⟩
    · rw [hSTu, if_pos hw]; exact Hok.live_st w (Or.inr (Or.inl hw))
    · rw [hSTu] at hw
      split at hw
      · rename_i hu
        have := Hbd w st hw hu
        refine ⟨by rw [show sint.Z (W64 (-1) : w64) = -1 by decide]; omega, by rw [hcur]; omega, ?_⟩
        exact (Hok.st_flags w st hw).2.1
      · cases hw
  iunfold mvcc.ownStates at Hstu
  have hne_of : ∀ W : GMap Loc mvcc.WatchRange, GMap.size W ≠ 0 → ∃ w, (W !! w).isSome := by
    intro W h
    refine Classical.byContradiction fun hc => h ?_
    rw [GMap.map_size_empty_iff, ← GMap.lookup_empty_iff]
    intro k
    cases hk : W !! k with
    | none => rfl
    | some _ => exact absurd ⟨k, by rw [hk]; rfl⟩ hc
  ihave Hch : ∃ (self : Bool) (W' : GMap Loc mvcc.WatchRange),
      ⌜W' ⊆ σ.Wu ∧ (∃ w, (W' !! w).isSome) ∧
        sint.Z minRev = mvcc.minRevOf STu (domSet W') ∧
        (self = true → g = mvcc.unsyncedAddr s ∧ W' = σ.Wu) ∧ GMap.size W' ≤ 512⌝ ∗
      mvcc.ownWatcherGroup g W' ∗
      (if self then iprop(True) else mvcc.ownWatcherGroup (mvcc.unsyncedAddr s) σ.Wu) $$ [Hch]
  · icases Hch with (⟨%H1, Hg, %Hm⟩ | ⟨%W', %H2, Hun, Hg, %Hm⟩)
    · iexists true, σ.Wu
      obtain ⟨rfl, hszlt⟩ := H1
      iframe Hg
      isplitr
      · ipureintro
        refine ⟨GMap.map_subseteq_refl _, hne_of _ (fun h => Hif (by rw [h]; rfl)), Hm,
          fun _ => ⟨rfl, rfl⟩, ?_⟩
        have h512 : sint.Z (W64 512 : w64) = 512 := by decide
        have := hszlt; rw [h512] at this; omega
      simp only [↓reduceIte]
      itrivial
    · iexists false, W'
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hg Hun
      ipureintro
      have h512 : sint.Z (W64 512 : w64) = 512 := by decide
      have := H2.2.2
      rw [h512] at this
      refine ⟨H2.1, hne_of _ ?_, Hm, (fun h => by cases h), by omega⟩
      omega
  icases Hch with ⟨%self, %W', %HW', Hg, Hun⟩
  obtain ⟨hW'sub, hW'ne, -, hself, hW'sz⟩ := HW'
  have hW'Wu : ∀ w r, W' !! w = some r → σ.Wu !! w = some r := fun w r h => hW'sub w r h
  have hW'ST : ∀ w, (W' !! w).isSome → ∃ st, STu !! w = some st ∧ σ.ST !! w = some st := by
    intro w hw
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hw
    have hu : (σ.Wu !! w).isSome := by rw [hW'Wu w r hr]; rfl
    obtain ⟨st, hst⟩ := Option.isSome_iff_exists.1 (Hok.live_st w (Or.inr (Or.inl hu)))
    exact ⟨st, by rw [hSTu, if_pos hu]; exact hst, hst⟩
  -- the cohorts of the chosen watchers
  wp_apply (hCoh g W' STu (W64 (-1))) $$ [$Hg Hstu] as %cs ⟨%L, Hg, Hstu, Hcs, Hcg, %HL⟩
  · iunfold mvcc.ownStates; iframe Hstu
    ipureintro
    refine ⟨fun w hw => ?_, fun w st' hw hs => ?_, by omega⟩
    · obtain ⟨st, h1, -⟩ := hW'ST w hw; rw [h1]; rfl
    · obtain ⟨st0, h1, h2⟩ := hW'ST w hw
      obtain rfl : st0 = st' := Option.some.inj (h1.symm.trans hs)
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hw
      exact (Hbd w st0 h2 (by rw [hW'Wu w r hr]; rfl)).1
  iunfold mvcc.ownStates at Hstu
  ihave Hst := (mvcc.sw_bigSepM_split (fun k _ => (σ.Wu !! k).isSome) σ.ST _).2 $$ [Hstu Hstr]
  · rw [hSTuD]; iframe
  ihave Hunsynced : mvcc.ownWatcherGroup (mvcc.unsyncedAddr s) σ.Wu $$ [Hg Hun]
  · cases hs : self
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at *; iexact Hun
    · obtain ⟨rfl, rfl⟩ := hself hs; iexact Hg
  ihave HP : mvcc.watchStoreBody s γ 1 σ $$ [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo
      Hmeta Hwt Hmem]
  · iunfold mvcc.watchStoreBody; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hvlen, Hok⟩
  ihave %Hcsl := ownSlice_len _ _ _ $$ Hcs
  rw [List.length_map] at Hcsl
  ihave IH : iprop(∃ (n : w64) (cv : revCohort) (σv : mvcc.WsState),
      "i" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ cv ∗
      "HP" ∷ mvcc.watchStoreBody s γ 1 σv ∗ "HrtR" ∷ mvcc.storeRT γ.st ∗
      "HbucketQ" ∷ mvcc.bucketView γ.st sync.rfrac.half (mvcc.bucketMap C) ∗
      "HlogQ" ∷ mvcc.idxLogAuth γ.st.idx (mvcc.revQ γ.st sync.rfrac) C ∗
      "Hcg" ∷ ([∗list] c ∈ L.drop (sint.nat n), mvcc.ownWatcherGroup c.wg c.W) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (L.length : Int) ∧
        (∀ w r, σv.Wu !! w = some r → σ.Wu !! w = some r) ∧
        ∀ c ∈ L.drop (sint.nat n), ∀ w, (c.W !! w).isSome →
          σv.Wu !! w = σ.Wu !! w ∧ σv.ST !! w = σ.ST !! w⌝) $$ [i c HP HrtR HbucketQ HlogQ Hcg]
  · iexists W64 0, _, σ
    simp only [named]
    iframe
    ipureintro
    exact ⟨by decide, by word, fun _ _ h => h, fun _ _ _ _ => ⟨trivial, trivial⟩⟩
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z cs.len := by
      revert Hif; simp
    have Hlt : sint.nat n < L.length := by word
    obtain ⟨c0, Hc0⟩ : ∃ c0, L[sint.nat n]? = some c0 := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z cs.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index cs (sint.Z n) (L.map mvcc.Cohort.val) (DFrac.own 1) c0.val Hn.1 $$ [Hcs]
      as Hcs
    · iframe; ipureintro; rw [List.getElem?_map, Hc0]; rfl
    (try wp_auto)
    -- the cohort's facts: its anchor is an unsynced member, at or above `0`, below `len(C)`
    have hc0mem : c0 ∈ L := List.mem_of_getElem? Hc0
    obtain ⟨wa, sta, hwa, hsta, hstaeq⟩ := HL.anchor c0 hc0mem
    have hwaW' : (W' !! wa).isSome := by
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hwa
      rw [HL.sub c0 hc0mem wa r hr]; rfl
    obtain ⟨sta', h1, h2⟩ := hW'ST wa hwaW'
    obtain rfl : sta' = sta := Option.some.inj (h1.symm.trans hsta)
    have hbd_a := Hbd wa sta' h2 (by
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hwaW'; rw [hW'Wu wa r hr]; rfl)
    have hc0lo : 0 ≤ sint.Z c0.minRev := by rw [← hstaeq]; exact hbd_a.1
    have hc0hi : sint.Z c0.minRev < C.length := by rw [← hstaeq]; exact hbd_a.2
    have hc0cur : sint.Z c0.minRev ≤ sint.Z (W64 ((C.length : Int) - 1)) := by rw [hcur]; omega
    simp only [mvcc.Cohort.val]
    rw [decide_eq_true hc0cur]
    wp_auto
    have h1000 : sint.Z (W64 1000 : w64) = 1000 := by decide
    -- the scan's end `m`: the current revision + 1, or `watchBatchMaxRevs + 1` past the start
    have hc0eq : L[sint.nat n] = c0 := Option.some.inj ((List.getElem?_eq_getElem Hlt).symm.trans Hc0)
    have hdrop : L.drop (sint.nat n) = c0 :: L.drop (sint.nat n + 1) := by
      rw [List.drop_eq_getElem_cons Hlt, hc0eq]
    have hc0d : c0 ∈ L.drop (sint.nat n) := by rw [hdrop]; exact List.mem_cons_self
    have hdisj := List.pairwise_cons.1 (HL.disj.sublist (hdrop ▸ List.drop_sublist _ _))
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have hsub : sint.Z (W64 ((C.length : Int) - 1) - c0.minRev) =
        (C.length : Int) - 1 - sint.Z c0.minRev := by rw [← hcur]; word
    wp_if_destruct
    all_goals (try wp_auto)
    all_goals first
      | (have _hbig : sint.Z (W64 1000 : w64) <
            sint.Z (W64 ((C.length : Int) - 1) - c0.minRev) := Hif
         generalize hm : c0.minRev + W64 1000 + W64 1 = m at *
         have hmF : sint.Z c0.minRev < sint.Z m ∧ sint.Z m ≤ C.length ∧
             (sint.Z m = C.length ∨ sint.Z m = sint.Z c0.minRev + 1001) ∧
             sint.Z m ≤ sint.Z c0.minRev + 1001 := by
           rw [hsub, h1000] at Hif
           rw [← hm]; refine ⟨by word, by word, Or.inr (by word), by word⟩
         clear hm)
      | (have _hsmall : ¬ sint.Z (W64 1000 : w64) <
            sint.Z (W64 ((C.length : Int) - 1) - c0.minRev) := Hif
         generalize hm : W64 ((C.length : Int) - 1) + W64 1 = m at *
         have hmF : sint.Z c0.minRev < sint.Z m ∧ sint.Z m ≤ C.length ∧
             (sint.Z m = C.length ∨ sint.Z m = sint.Z c0.minRev + 1001) ∧
             sint.Z m ≤ sint.Z c0.minRev + 1001 := by
           rw [hsub, h1000] at Hif
           rw [← hm]; refine ⟨by word, by word, Or.inl (by word), by word⟩
         clear hm)
    all_goals
      rw [hdrop]
      icases Hcg with ⟨Hc0g, Hcg⟩
      wp_apply (hSWC s st γ σv C c0.wg c0.W c0.minRev m)
        $$ [$HrtR $HbucketQ $HlogQ $HP $Hc0g] as ⟨%σ', HrtR, HbucketQ, HlogQ, HP, %Hfr⟩
      · iframe #
        ipureintro
        refine ⟨HneQ, hClt, hc0lo, by omega, hmF.2.1, ?_, fun w r hw => ?_, fun w st hw hs => ?_, ?_⟩
        · obtain ⟨w, st, hw, -, -⟩ := HL.anchor c0 hc0mem; exact ⟨w, hw⟩
        · rw [(Hn.2.2.2 c0 hc0d w (by rw [hw]; rfl)).1]
          exact hW'Wu w r (HL.sub c0 hc0mem w r hw)
        · rw [(Hn.2.2.2 c0 hc0d w hw).2] at hs
          obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hw
          have hwW' := HL.sub c0 hc0mem w r hr
          obtain ⟨st', h1, h2⟩ := hW'ST w (by rw [hwW']; rfl)
          obtain rfl : st' = st := Option.some.inj (h2.symm.trans hs)
          have hwin := HL.window c0 hc0mem w st' hw h1
          have hb := Hbd w st' h2 (by rw [hW'Wu w r hwW']; rfl)
          refine ⟨hwin.1, ?_⟩
          rcases hmF.2.2.1 with h | h <;> omega
        · -- the scan's bound: `watchBatchMaxRevs + 1` revisions
          exact hmF.2.2.2
      wp_for_post
      iframe
      iexists n + W64 1, _, σ'
      simp only [named]
      rw [hn1]
      iframe
      ipureintro
      refine ⟨by word, by word, fun w r h => Hn.2.2.1 w r (Hfr.1 w r h), fun d hd w hw => ?_⟩
      have hdn : d ∈ L.drop (sint.nat n) := by rw [hdrop]; exact List.mem_cons_of_mem _ hd
      have hc0w : c0.W !! w = none := by
        cases h : c0.W !! w with
        | none => rfl
        | some _ =>
          have := hdisj.1 d hd w (by rw [h]; rfl)
          rw [this] at hw; cases hw
      obtain ⟨e1, e2⟩ := Hfr.2 w hc0w
      obtain ⟨e3, e4⟩ := Hn.2.2.2 d hdn w hw
      exact ⟨e1.trans e3, e2.trans e4⟩
  -- the cohorts done: the gauge over the victims and the unsynced watchers left
  iunfold mvcc.watchStoreBody at HP
  iNamed HP
  wp_auto
  ihave %Hvsl := ownSlice_len _ _ _ $$ Hvs
  ihave IH2 : iprop(∃ (k vz : w64) (vv : GoMap),
      "i" ∷ i_ptr ↦ k ∗ "vsz" ∷ vsz_ptr ↦ vz ∗ "v" ∷ v_ptr ↦ vv ∗ "Hvs" ∷ σv.vs ↦* σv.vbs ∗
      "Hvbs" ∷ ([∗list] x ∈ σv.vbs.zip σv.VB, mvcc.ownWatcherBatch x.1 x.2) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z σv.vs.len⌝) $$ [i vsz v Hvs Hvbs]
  · iexists W64 0, W64 0, _
    simp only [named]
    iframe
    ipureintro; exact ⟨by decide, Hvsl.2⟩
  wp_for IH2
  wp_if_destruct
  · have Hlt : sint.nat k < σv.vbs.length := by rw [Hvsl.1]; word
    obtain ⟨vmap, Hvn⟩ : ∃ vmap, σv.vbs[sint.nat k]? = some vmap :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z σv.vs.len := ⟨Hk.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index σv.vs (sint.Z k) σv.vbs (DFrac.own 1) vmap Hk.1 $$ [Hvs] as Hvs
    · iframe; ipureintro; exact Hvn
    (try wp_auto)
    obtain ⟨Bn, HBn⟩ : ∃ Bn, σv.VB[sint.nat k]? = some Bn :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hvlen]; exact Hlt)⟩
    have hz : (σv.vbs.zip σv.VB)[sint.nat k]? = some (vmap, Bn) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨Hvn, HBn⟩
    icases (BigSepL.bigSepL_lookup_acc hz).1 $$ Hvbs with ⟨Hb, Hback⟩
    iunfold mvcc.ownWatcherBatch at Hb
    icases Hb with ⟨%PBn, Hbm, %HBn', Hbs⟩
    wp_apply wp_map_len_lt $$ Hbm as ⟨Hbm, -⟩
    (try wp_auto)
    wp_for_post_core
    ihave Hvbs := Hback $$ [Hbm Hbs]
    · iunfold mvcc.ownWatcherBatch; iexists PBn; iframe; ipureintro; exact HBn'
    (try wp_auto)
    iframe
    iexists k + W64 1, _, _
    simp only [named]
    iframe
    isplitl [Hvbs]
    · rw [mvcc.set_same hz]; iexact Hvbs
    ipureintro; constructor <;> word
  wp_apply (hSize (mvcc.unsyncedAddr s) σv.Wu 1) $$ [$Hunsynced] as ⟨Hunsynced, -⟩
  (try wp_auto)
  iunfold gaugeSetSpec at HgSet
  rw [HgEq]
  wp_apply HgSet
  (try wp_auto)
  wp_apply (hSize (mvcc.unsyncedAddr s) σv.Wu 1) $$ [$Hunsynced] as ⟨Hunsynced, -⟩
  (try wp_auto)
  -- the deferred `s.store.revMu.RUnlock()`
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HrevQ HclogQ HbucketQ HtoksQ HlogQ HcmpQ HcrevQ]
    as HrevMuR
  · inext
    iunfold mvcc.revMuInv
    iexists C, ntok, -1
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨HneQ, HbudgetQ, HcQ⟩
  (try wp_auto)
  -- the lock's final state
  ihave HPf : mvcc.watchStoreBody s γ 1 σv $$ [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo
      Hmeta Hwt Hmem]
  · iunfold mvcc.watchStoreBody
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨Hvlen, Hok⟩
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl HPf]
  · inext; iunfold mvcc.watchStoreInv; iexists σv; iexact HPf
  (try wp_auto)
  iapply HΦ
  iunfold mvcc.watchReader
  iframe Hmur
  iunfold mvcc.storeReader
  iexists _
  simp only [named]
  iframe
  iframe #

end proof
end EtcdGrove
end Perennial
