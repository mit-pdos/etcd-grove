/-
Proof of `Spec/.../mvcc/watchableStore__syncWatcherCohort.lean`. Lean-first (no Rocq
counterpart). The loop is `syncWatchers`' before etcd-io/etcd#22304 (`lean`'s
`watchableStore__syncWatchers.lean`), over the cohort's own group (never the unsynced group
itself), for the scan `[minRev, maxScanRev)`, with the PR's new cases when the scan did not
reach the current revision (`reachedCurRev = false`): a member stays unsynced at `maxScanRev`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__syncWatcherCohort
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.rangeEvents
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherBatch
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcher__send
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__add
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__delete
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__addVictim
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

/-- The builtin `max` on `int64`. -/
theorem mvcc.swc_wp_max_int64 (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.int64, go.int64])) (Val #x)) (Val #y))
    {{ RET #(if sint.Z y < sint.Z x then x else y); True }} := by
  wp_start
  by_cases h : sint.Z y < sint.Z x
  · rw [decide_eq_true h, if_pos h]; wp_auto; iapply HΦ; itrivial
  · rw [decide_eq_false h, if_neg h]; wp_auto; iapply HΦ; itrivial

/-- A step of the loop keeps the unsynced members within the lock's (`σ`). -/
theorem mvcc.swc_step_Wu_sub (σWu : GMap Loc mvcc.WatchRange) (v : mvcc.SyncVars) (key : Loc)
    (r : mvcc.WatchRange) (dst : mvcc.SyncDst) (st' : mvcc.WatcherSt) (e' : List mvcc.EvM × Nat)
    (h : ∀ w r, v.Wu !! w = some r → σWu !! w = some r) :
    ∀ w r', (v.step key r dst st' e').Wu !! w = some r' → σWu !! w = some r' := by
  intro w r' hw
  cases dst with
  | unsynced => exact h w r' hw
  | synced =>
    simp only [mvcc.SyncVars.step] at hw
    by_cases hk : key = w
    · subst hk; rw [GMap.lookup_delete] at hw; cases hw
    · rw [GMap.lookup_delete_ne _ hk] at hw; exact h w r' hw
  | victim B =>
    simp only [mvcc.SyncVars.step] at hw
    by_cases hk : key = w
    · subst hk; rw [GMap.lookup_delete] at hw; cases hw
    · rw [GMap.lookup_delete_ne _ hk] at hw; exact h w r' hw

set_option maxRecDepth 20000 in
theorem mvcc.watchableStore.syncWatcherCohort.wp_proof
    (hRange : mvcc.rangeEvents.spec (GF := GF) (hG := hG))
    (hNWB : mvcc.newWatcherBatch.spec (GF := GF) (hG := hG))
    (hSend : mvcc.watcher.send.spec (GF := GF) (hG := hG))
    (hAdd : mvcc.watcherGroup.add.spec (GF := GF) (hG := hG))
    (hDel : mvcc.watcherGroup.delete.spec (GF := GF) (hG := hG))
    (hAddV : mvcc.watchableStore.addVictim.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.syncWatcherCohort.spec (GF := GF) (hG := hG) := by
  have hAddG := mvcc.watcherGroup.add.spec_group hAdd
  have hDelG := mvcc.watcherGroup.delete.spec_group hDel
  intro s st γ σ C g W' minRev maxScanRev
  wp_start as ⟨#Hws, HrtR, #HfrzR, HbucketQ, #HcertQ, #HokQ, HlogQ, HP, Hg, %Hpre⟩
  obtain ⟨HneQ, hClt, hmin0, hminmax, hmaxC, hW'ne, hW'Wu, hW'b, -⟩ := Hpre
  ihave #HwsAll : mvcc.isWatchableStore s st γ $$ []
  · iexact Hws
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨%gP, #HgP, #HgPS⟩, -⟩
  iunfold mvcc.watchStoreBody at HP
  iNamed HP
  icases mvcc.watchBudget_bound _ _ _ $$ Hwt with ⟨Hwt, %HMb⟩
  ihave #Hs0 : mvcc.isStore st γ.st $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamedSuffix Hs "S"
  icases persistent_entails_right (mvcc.idxLogAuth_cert_prefix _ _ _ _) $$ [$HlogQ $Hcert]
    with ⟨%HpC, HlogQ, -⟩
  -- the unsynced members' states
  icases persistent_entails_right (mvcc.sw_unsynced_bounds γ σ Hok _ C) $$ [$Hmem $HlogQ]
    with ⟨%Hbd, Hmem, HlogQ⟩
  have hCne : 1 ≤ C.length := List.length_pos_iff.2 HneQ
  icases (mvcc.sw_bigSepM_split (fun k _ => (σ.Wu !! k).isSome) σ.ST _).1 $$ Hst with ⟨Hstu, Hstr⟩
  have hSTu : ∀ k, (Iris.Std.PartialMap.filter (fun k _ => (σ.Wu !! k).isSome) σ.ST : GMap Loc mvcc.WatcherSt) !! k =
      if (σ.Wu !! k).isSome then σ.ST !! k else none := by
    intro k; rw [mvcc.sw_filter_lookup]; cases σ.ST !! k <;> cases (σ.Wu !! k).isSome <;> rfl
  generalize hSTuD : (Iris.Std.PartialMap.filter (fun k _ => (σ.Wu !! k).isSome) σ.ST : GMap Loc mvcc.WatcherSt) = STu at hSTu ⊢
  have hcur : sint.Z (W64 ((C.length : Int) - 1)) = (C.length : Int) - 1 := by word
  have hW'ST : ∀ w, (W' !! w).isSome → ∃ st, STu !! w = some st ∧ σ.ST !! w = some st := by
    intro w hw
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hw
    have hu : (σ.Wu !! w).isSome := by rw [hW'Wu w r hr]; rfl
    obtain ⟨st, hst⟩ := Option.isSome_iff_exists.1 (Hok.live_st w (Or.inr (Or.inl hu)))
    exact ⟨st, by rw [hSTu, if_pos hu]; exact hst, hst⟩
  ihave %HCwf : ⌜mvcc.LogWf' C ∧ C.length < 2 ^ 63 ∧ ∀ cs ∈ C, cs.length < 2 ^ 63⌝ $$ [HcertQ]
  · iunfold mvcc.idxCert at HcertQ
    icases HcertQ with ⟨-, -, %H, -⟩
    ipureintro; exact H
  -- the scan's end, as a number
  generalize hNdef : sint.nat maxScanRev = N
  have hN : (N : Int) = sint.Z maxScanRev := by
    rw [← hNdef]; show ((sint.Z maxScanRev).toNat : Int) = _; omega
  have hNC : N ≤ C.length := by omega
  have hmn : sint.nat minRev ≤ N := by
    rw [← hNdef]; show (sint.Z minRev).toNat ≤ (sint.Z maxScanRev).toNat; omega
  wp_auto
  wp_apply (hRange _ _ γ.st _ _ _ _ C minRev maxScanRev g W')
    $$ [$HbkS $HrtR $HfrzR $HbucketQ $HcertQ $Hg] as %evs ⟨HrtR, HbucketQ, Hg, %ps, Hevs, Hevcap,
      %Hpslen, #HevIs⟩
  · ipureintro; omega
  rw [hNdef] at Hpslen ⊢
  generalize hevm : (mvcc.logEvents C (sint.nat minRev) N).filter
    (fun ev => mvcc.wgCovers W' ev.kv.key) = evm at Hpslen ⊢
  (try wp_auto)
  rw [go.make1_underlying, go.is_underlying (t := watcherBatch.ty)]
  wp_apply (wp_map_make1 (K := Loc) (V := Loc)) as %vm Hvm
  (try wp_auto)
  wp_apply (hNWB g W' STu evs (DFrac.own 1) ps evm) $$ [$Hg Hstu $Hevs $HevIs]
    as %wb ⟨Hg, Hstu, Hevs, Hwb⟩
  · iunfold mvcc.ownStates; iframe Hstu
    ipureintro
    refine ⟨fun w hw => ?_, Hpslen⟩
    obtain ⟨st, h1, -⟩ := hW'ST w hw; rw [h1]; rfl
  icases Hwb with (%hW0 | ⟨-, Hwb⟩)
  · exfalso; obtain ⟨w, hw⟩ := hW'ne; rw [hW0.1] at hw; cases hw
  iunfold mvcc.ownStates at Hstu
  ihave Hst := (mvcc.sw_bigSepM_split (fun k _ => (σ.Wu !! k).isSome) σ.ST _).2 $$ [Hstu Hstr]
  · rw [hSTuD]; iframe
  -- the cohort's set, lent to the loop
  icases (mvcc.ownWatcherGroup_at g W' 1).1 $$ Hg with ⟨%ws, Hg⟩
  iunfold mvcc.ownWatcherGroupAt at Hg
  icases Hg with ⟨%km, %t, %KM, %L, Hg⟩
  iNamed Hg
  wp_auto
  iunfold mvcc.ownWatcherSet at Hws
  iunfold mvcc.ownWatcherBatch at Hwb
  icases Hwb with ⟨%PB, Hwbm, %HBt, Hbs⟩
  have hcur1 : sint.Z (W64 ((C.length : Int) - 1) + W64 1) = (C.length : Int) := by word
  have hreach : (maxScanRev = W64 ((C.length : Int) - 1) + W64 1) ↔ sint.Z maxScanRev = C.length := by
    constructor
    · intro h; rw [h]; exact hcur1
    · intro h; word
  generalize hreachD : decide (maxScanRev = W64 ((C.length : Int) - 1) + W64 1) = reached
  have hreached : reached = true ↔ sint.Z maxScanRev = C.length := by
    rw [← hreachD, decide_eq_true_iff]; exact hreach
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range_gen (K := Loc) (V := Unit)
    (fun (keys : List Loc) (i : Nat) (m' : GMap Loc Unit) => iprop(
      ∃ (v : mvcc.SyncVars) (PBv PBr : GMap Loc (Loc × mvcc.EventBatch)) (wv : Loc),
      "Hst" ∷ ([∗map] w ↦ x ∈ v.ST, mvcc.watcherOwn w x) ∗
      "Hmem" ∷ ([∗map] w ↦ x ∈ v.ST, mvcc.memberRes γ 1 (v.st σ) w x) ∗
      "Hsynced" ∷ mvcc.ownWatcherGroup (mvcc.syncedAddr s) v.Ws ∗
      "Hun" ∷ mvcc.ownWatcherGroup (mvcc.unsyncedAddr s) v.Wu ∗
      "Hvm" ∷ vm ↦$ GMap.fmap Prod.fst PBv ∗
      "Hbv" ∷ ([∗map] _w ↦ p ∈ PBv, ⌜p.1 ≠ null⌝ ∗ mvcc.ownEventBatch p.1 p.2) ∗
      "Hrem" ∷ ([∗map] _w ↦ p ∈ PBr, ⌜p.1 ≠ null⌝ ∗ mvcc.ownEventBatch p.1 p.2) ∗
      "Hwbm" ∷ wb ↦$ GMap.fmap Prod.fst PB ∗
      "w" ∷ w_ptr ↦ wv ∗ "s" ∷ s_ptr ↦ s ∗
      "curRev" ∷ curRev_ptr ↦ W64 ((C.length : Int) - 1) ∗
      "compactionRev" ∷ compactionRev_ptr ↦ W64 (-1) ∗
      "maxScanRev" ∷ maxScanRev_ptr ↦ maxScanRev ∗
      "reachedCurRev" ∷ reachedCurRev_ptr ↦ reached ∗
      "victims" ∷ victims_ptr ↦ vm ∗ "wb" ∷ wb_ptr ↦ wb ∗
      "%Hi" ∷ ⌜mvcc.SyncLoop σ v PB PBv PBr keys i ∧ m' = domSet W' ∧
        ∀ w r, v.Wu !! w = some r → σ.Wu !! w = some r⌝))
    _ _ _ ws (domSet W') (DFrac.own 1)) $$ Hws
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hst Hmem Hsynced Hunsynced Hvm Hbs Hwbm w s curRev compactionRev maxScanRev
    reachedCurRev victims wb]
  · iexists mvcc.SyncVars.init σ, ∅, PB, zero_val Loc
    simp only [named, GMap.fmap_empty]
    have hI : ∀ k, (mvcc.SyncVars.st σ (mvcc.SyncVars.init σ)).victimOf k = σ.victimOf k := by
      intro k; rw [mvcc.SyncVars.st_victimOf]; simp [mvcc.SyncVars.init]
    iframe Hvm Hwbm w s curRev compactionRev maxScanRev reachedCurRev victims wb Hbs
    have e1 : (mvcc.SyncVars.init σ).ST = σ.ST := rfl
    have e2 : (mvcc.SyncVars.init σ).Ws = σ.Ws := rfl
    have e3 : (mvcc.SyncVars.init σ).Wu = σ.Wu := rfl
    rw [e1, e2, e3]
    iframe Hst Hsynced Hunsynced
    isplitl [Hmem]
    · iapply (BigSepM.bigSepM_mono (fun {k x} _ => ?_)) $$ Hmem
      rw [mvcc.sw_memberRes_congr γ 1 (mvcc.SyncVars.st σ (mvcc.SyncVars.init σ)) σ k x
        rfl rfl rfl rfl (hI k)]
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    ipureintro
    exact ⟨⟨Hok.sync_init, by rw [GMap.fmap_empty]; rfl, fun k _ => by
      simp [mvcc.SyncVars.init]⟩, by trivial, fun w r h => h⟩
  isplitr
  · imodintro
    iintro %i %key %u %m' ⟨%Hkey, %Hu⟩ HP Hm
    iNamed HP
    obtain ⟨Hl, hm', hsub⟩ := Hi
    have hnot := mvcc.sw_not_mem_take keys Hknodup i key Hkey
    have hW : (W' !! key).isSome := by
      have := (Hkset key).1 (List.mem_of_getElem? Hkey)
      rw [GMap.domSet, GMap.lookup_fmap] at this; simpa using this
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hW
    obtain ⟨st, hSTuk, hσST⟩ := hW'ST key hW
    have hσWu : σ.Wu !! key = some r := hW'Wu key r hr
    obtain ⟨hvST, hvWu, hvWs, hvE, hvBv, hPBr⟩ := Hl.rest key hnot
    rw [hσST] at hvST
    rw [hσWu] at hvWu
    have hσWs : σ.Ws !! key = none := by
      cases h : σ.Ws !! key with
      | none => rfl
      | some _ => have := Hok.ws_wu key (by rw [h]; rfl); rw [hσWu] at this; cases this
    rw [hσWs] at hvWs
    obtain ⟨hm0', hmC⟩ := Hbd key st hσST (by rw [hσWu]; rfl)
    obtain ⟨hmlo, hmhi⟩ := hW'b key st hW hσST
    have hvST' : Iris.Std.PartialMap.get? v.ST key = some st := by rw [gmap_get?_eq]; exact hvST
    icases (BigSepM.bigSepM_delete hvST').1 $$ Hst with ⟨Hstw, Hst⟩
    icases (BigSepM.bigSepM_delete hvST').1 $$ Hmem with ⟨Hmemw, Hmem⟩
    icases mvcc.sw_memberRes_unsynced γ 1 (v.st σ) key st hvWs (by show (v.Wu !! key).isSome; rw [hvWu]; rfl)
      $$ Hmemw with ⟨%γw, %r', %fcs, %evsw, %hM, #Hmeta, #Hfx, #Hch, #Hfo, %Hsr, %hE, Ha, Hlv, %Hlo,
        #Hwf, %Lc, #HLc, %HLc⟩
    icases (BigSepM.bigSepM_lookup_acc (m := W') (by rw [gmap_get?_eq]; exact hr)).1 $$ Hfixed
      with ⟨⟨%fcs0, #Hf0⟩, -⟩
    ihave %Hag := mvcc.watcherFixed_agree key r' r fcs fcs0 $$ [$Hfx $Hf0]
    obtain ⟨rfl, -⟩ := Hag
    iunfold mvcc.watcherOwn at Hstw
    icases Hstw with ⟨HminRev, Hvict, Hcomp, Hrest0, Hchf⟩
    wp_auto
    rw [decide_eq_false (show ¬ sint.Z st.minRev < sint.Z (W64 (-1) : w64) by
      rw [show sint.Z (W64 (-1) : w64) = -1 by decide]; omega)]
    wp_auto
    wp_apply mvcc.swc_wp_max_int64
    rw [if_pos (show sint.Z st.minRev < sint.Z maxScanRev by omega)]
    (try wp_auto)
    wp_apply wp_map_lookup2 $$ Hwbm as Hwbm
    have hbk : GMap.fmap Prod.snd PB !! key = mvcc.memberBatch r' st evm := by
      rw [← HBt, mvcc.batchOf_lookup, hr, hSTuk]
    have hmb := mvcc.memberBatch_logEvents C HCwf.1 HCwf.2.1 HCwf.2.2 r' st
      (fun ev => mvcc.wgCovers W' ev.kv.key) (sint.nat minRev) N
      (fun ev hc => by
        simp only [mvcc.wgCovers, decide_eq_true_eq]; exact ⟨key, r', hr, hc⟩)
      (by show ((sint.Z minRev).toNat : Int) ≤ _; omega)
      hNC
    rw [hevm] at hmb
    have hmN : sint.nat st.minRev ≤ N := by
      show (sint.Z st.minRev).toNat ≤ _; omega
    have hloN : γw.lo ≤ sint.nat st.minRev := by
      show _ ≤ (sint.Z st.minRev).toNat; omega
    have hmz : (sint.nat st.minRev : Int) = sint.Z st.minRev := by
      show ((sint.Z st.minRev).toNat : Int) = _; omega
    obtain ⟨fc, fr, fv, fch, fvo, fbv, -⟩ := Hl.unsynced_facts hvWu hvST
    rcases hmb with ⟨hnone, hwE⟩ | ⟨B, hsome, hBne, hBev⟩
    · -- no batch
      rw [hnone, GMap.lookup_fmap] at hbk
      have hPBk : PB !! key = none := by
        cases h : PB !! key with
        | none => rfl
        | some _ => rw [h] at hbk; cases hbk
      rw [hPBk]
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, decide_false,
        Bool.not_false]
      wp_auto
      ihave #Hwf' := mvcc.sw_evsWf_extend γ r' γw.lo evsw (sint.nat st.minRev) N C hmN
        hNC hloN $$ [$Hwf $HcertQ $HokQ]
      rw [hwE, List.append_nil] at *
      generalize hst' : ({ st with minRev := maxScanRev } : mvcc.WatcherSt) = st'
      have hst'm : sint.Z st'.minRev = N := by rw [← hst']; exact hN.symm
      cases hr : reached
      · -- the scan did not reach the current revision: stays unsynced at `maxScanRev`
        (try simp only [Bool.false_eq_true, ↓reduceIte])
        (try wp_auto)
        have hNlt : (N : Int) < C.length := by
          have : ¬ sint.Z maxScanRev = C.length := fun h => by
            have := hreached.2 h; rw [hr] at this; cases this
          omega
        ihave Hmw := mvcc.sw_memberRes_new_unsynced γ σ v key r' st' γw fcs evsw N C
          hM Hsr hvWs hvWu ⟨by rw [hst'm]; omega, by
            show N = (sint.Z st'.minRev).toNat; rw [hst'm]; simp⟩ (by rw [hst'm]; exact hNlt)
          $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf']
        · rw [← hst']; iframe; iframe #
        ihave Hwo : mvcc.watcherOwn key st' $$ [HminRev Hvict Hcomp Hrest0 Hchf]
        · rw [← hst']; iunfold mvcc.watcherOwn; iframe
        icases mvcc.sw_res_step γ σ v key r' .unsynced st' (evsw, N)
          $$ [$Hst $Hwo $Hmem $Hmw] with ⟨Hst, Hmem⟩
        have hok' := Hl.ok.sync_step hvWu hvST .unsynced st' (evsw, N)
          ⟨by rw [← hst']; exact fc, by rw [← hst']; exact fr, by rw [← hst'], by rw [← hst']; exact fv⟩
          (fun h => by cases h)
        unfold forMapPostcondition
        ileft
        isplitr
        · ipureintro; rfl
        iexists _
        iframe Hm
        iexists v.step key r' .unsynced st' (evsw, N), PBv, PBr, key
        simp only [named]
        have e1 : (v.step key r' .unsynced st' (evsw, N)).Ws = v.Ws := rfl
        have e2 : (v.step key r' .unsynced st' (evsw, N)).Wu = v.Wu := rfl
        rw [e1, e2]
        iframe Hst Hmem Hsynced Hun Hvm Hbv Hrem Hwbm w s curRev compactionRev maxScanRev
          reachedCurRev victims wb
        ipureintro
        exact ⟨Hl.step Hkey r' .unsynced st' (evsw, N) PBv PBr hok' Hl.bv (fun _ _ => rfl), hm',
          mvcc.swc_step_Wu_sub _ v key r' .unsynced st' (evsw, N) hsub⟩
      · -- reached: synced
        (try simp only [↓reduceIte])
        (try wp_auto)
        have hNC' : N = C.length := by have := hreached.1 hr; omega
        subst hNC'
        wp_apply (hAddG (mvcc.syncedAddr s) v.Ws key r' fcs) $$ [$Hsynced $Hfx] as Hsynced
        · ipureintro; exact ⟨hvWs, by have := Hl.ok.ws_size; simp only [mvcc.SyncVars.st] at this; omega⟩
        (try wp_auto)
        wp_apply (hDelG (mvcc.unsyncedAddr s) v.Wu key r' fcs) $$ [$Hun $Hfx] as Hun
        (try wp_auto)
        ihave Hmw := mvcc.sw_memberRes_new_synced γ σ v key r' st' γw fcs evsw C.length hM Hsr
          ⟨by rw [hst'm]; omega, by rw [hst'm]; exact Int.le_refl _⟩ $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf']
        · rw [← hst']; iframe; iframe #
        ihave Hwo : mvcc.watcherOwn key st' $$ [HminRev Hvict Hcomp Hrest0 Hchf]
        · rw [← hst']; iunfold mvcc.watcherOwn; iframe
        icases mvcc.sw_res_step γ σ v key r' .synced st' (evsw, C.length) $$ [$Hst $Hwo $Hmem $Hmw]
          with ⟨Hst, Hmem⟩
        have hok' := Hl.ok.sync_step hvWu hvST .synced st' (evsw, C.length)
          ⟨by rw [← hst']; exact fc, by rw [← hst']; exact fr, by rw [← hst'], by rw [← hst']; exact fv⟩
          (fun _ γw' hM' => by
            rw [show σ.M !! key = some γw from hM] at hM'; cases hM'
            have := HpC.length_le
            simp only; omega)
        unfold forMapPostcondition
        ileft
        isplitr
        · ipureintro; rfl
        iexists _
        iframe Hm
        iexists v.step key r' .synced st' (evsw, C.length), PBv, PBr, key
        simp only [named]
        have e1 : (v.step key r' .synced st' (evsw, C.length)).Ws = <[key := r']> v.Ws := rfl
        have e2 : (v.step key r' .synced st' (evsw, C.length)).Wu = GMap.delete key v.Wu := rfl
        rw [e1, e2]
        iframe Hst Hmem Hsynced Hun Hvm Hbv Hrem Hwbm w s curRev compactionRev maxScanRev
          reachedCurRev victims wb
        ipureintro
        exact ⟨Hl.step Hkey r' .synced st' (evsw, C.length) PBv PBr hok' Hl.bv (fun _ _ => rfl), hm',
          mvcc.swc_step_Wu_sub _ v key r' .synced st' (evsw, C.length) hsub⟩
    · rw [hsome, GMap.lookup_fmap] at hbk
      obtain ⟨ebp, hPBk⟩ : ∃ ebp, PB !! key = some (ebp, B) := by
        cases h : PB !! key with
        | none => rw [h] at hbk; cases hbk
        | some p =>
          rw [h] at hbk; obtain ⟨p1, p2⟩ := p; simp at hbk; exact ⟨p1, by rw [hbk]⟩
      rw [hPBk]
      simp only [Option.map_some, Option.getD_some, Option.isSome_some, decide_true,
        Bool.not_true]
      have hPBrk : PBr !! key = some (ebp, B) := hPBr.trans hPBk
      icases (BigSepM.bigSepM_delete (by rw [gmap_get?_eq]; exact hPBrk)).1 $$ Hrem
        with ⟨⟨%Hebnn, HB⟩, Hrem⟩
      iunfold mvcc.ownEventBatch at HB
      icases HB with ⟨%sl, %eps, Heb, Hsl, Hcap, %Heplen, #HevB⟩
      simp only at Heplen ⊢
      ihave #Hfx0 := Hfx
      iunfold mvcc.watcherFixed at Hfx0
      icases Hfx0 with ⟨%Hwnn, %ks, %es', #Hk, #Hks, #He, #Hes, #Hsr', #Hid, #Hfcs⟩
      iunfold gaugeSpec at HgPS
      icases HgPS with ⟨-, -, #HgPA⟩
      have hPBv0 : PBv !! key = none := by
        have := fbv; rw [Hl.bv, GMap.lookup_fmap] at this
        cases h : PBv !! key with
        | none => rfl
        | some _ => rw [h] at this; cases this
      (try wp_auto)
      rcases hBev with ⟨hmr0, hevB⟩ | ⟨M, hmrM, hMm, hMC, hevB⟩
      · -- all of the scan's events
        rw [decide_eq_true hmr0]
        wp_auto
        ihave #Hwf' := mvcc.sw_evsWf_extend γ r' γw.lo evsw (sint.nat st.minRev) N C hmN
          hNC hloN $$ [$Hwf $HcertQ $HokQ]
        rw [← hevB]
        have hmodB := mvcc.watchEvents_modRev C HCwf.2.1 r' (sint.nat st.minRev) N hNC
        rw [← hevB] at hmodB
        wp_apply (hSend γ key γw r' fcs st.ch 1 (1 : Qp).half evsw N _ eps B.evs (DFrac.own 1))
          $$ [Hchf Hlv Ha Hsl] as %b ⟨Hchf, Hlv, Hsl, Ha⟩
        · rw [if_neg hBne]
          iframe Hmeta Hfx Hfo Hch Hchf Hlv Ha Hwf' Hsl HevB
          isplitr
          · ileft; ipureintro; rfl
          ipureintro
          refine ⟨Heplen, rfl, fun _ => rfl, fun ev hev => ?_, fun _ ev hev => ?_⟩
          · have := hmodB ev hev; rw [hcur]; omega
          · have := hmodB ev hev; omega
        rw [if_neg hBne]
        generalize hst' : ({ st with minRev := maxScanRev } : mvcc.WatcherSt) = st'
        have hst'm : sint.Z st'.minRev = N := by rw [← hst']; exact hN.symm
        cases b
        · -- a victim, at `maxScanRev`
          simp only [Bool.false_eq_true, ↓reduceIte]
          wp_auto
          wp_apply wp_mapInsert $$ Hvm as Hvm
          (try wp_auto)
          wp_apply (hDelG (mvcc.unsyncedAddr s) v.Wu key r' fcs) $$ [$Hun $Hfx] as Hun
          (try wp_auto)
          generalize hstv : ({ st' with victim := true } : mvcc.WatcherSt) = stv
          have hstvm : sint.Z stv.minRev = N := by rw [← hstv]; exact hst'm
          ihave Hmw := mvcc.sw_memberRes_new_victim γ σ v key r' B stv γw fcs evsw N
            hM Hsr hvWs fvo ⟨by rw [hstvm]; omega, by
              show N = (sint.Z stv.minRev).toNat; rw [hstvm]; simp,
              fun h => absurd hmr0 h, fun ev hev => by
                have := hmodB ev hev
                rw [hstvm]; omega⟩
            $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf']
          · rw [← hstv, ← hst']; iframe; iframe #
          ihave Hwo : mvcc.watcherOwn key stv $$ [HminRev Hvict Hcomp Hrest0 Hchf]
          · rw [← hstv, ← hst']; iunfold mvcc.watcherOwn; iframe
          icases mvcc.sw_res_step γ σ v key r' (.victim B) stv (evsw, N)
            $$ [$Hst $Hwo $Hmem $Hmw] with ⟨Hst, Hmem⟩
          have hok' := Hl.ok.sync_step hvWu hvST (.victim B) stv (evsw, N)
            ⟨by rw [← hstv, ← hst']; exact fc, by rw [← hstv, ← hst']; exact fr,
              by rw [← hstv, ← hst'], by rw [← hstv]; rfl⟩
            (fun h => by cases h)
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists _
          iframe Hm
          iexists v.step key r' (.victim B) stv (evsw, N), <[key := (ebp, B)]> PBv,
            Iris.Std.delete PBr key, key
          simp only [named]
          have e1 : (v.step key r' (.victim B) stv (evsw, N)).Ws = v.Ws := rfl
          have e2 : (v.step key r' (.victim B) stv (evsw, N)).Wu = GMap.delete key v.Wu := rfl
          rw [e1, e2, GMap.fmap_insert]
          iframe Hst Hmem Hsynced Hun Hvm Hrem Hwbm w s curRev compactionRev maxScanRev
            reachedCurRev victims wb
          isplitl [Hbv Heb Hsl Hcap]
          · iapply (BigSepM.bigSepM_insert (by rw [gmap_get?_eq]; exact hPBv0)).2
            iframe Hbv
            isplitr
            · ipureintro; exact Hebnn
            iunfold mvcc.ownEventBatch
            iexists sl, eps
            iframe Heb Hsl Hcap HevB
            ipureintro; exact Heplen
          ipureintro
          exact ⟨Hl.step Hkey r' (.victim B) stv (evsw, N) _ _ hok'
            (by show <[key := B]> v.Bv = _; rw [Hl.bv, GMap.fmap_insert])
            (fun k hk => by
              show (GMap.delete key PBr) !! k = _
              exact GMap.lookup_delete_ne _ (Ne.symm hk)), hm',
            mvcc.swc_step_Wu_sub _ v key r' (.victim B) stv (evsw, N) hsub⟩
        · -- sent
          simp only [↓reduceIte]
          wp_auto
          wp_apply HgPA
          (try wp_auto)
          rw [fv]
          wp_auto
          rw [decide_eq_true hmr0]
          wp_auto
          cases hr : reached
          · -- the scan did not reach the current revision: stays unsynced at `maxScanRev`
            (try simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false])
            (try wp_auto)
            have hNlt : (N : Int) < C.length := by
              have : ¬ sint.Z maxScanRev = C.length := fun h => by
                have := hreached.2 h; rw [hr] at this; cases this
              omega
            ihave Hmw := mvcc.sw_memberRes_new_unsynced γ σ v key r' st' γw fcs (evsw ++ B.evs) N C
              hM Hsr hvWs hvWu ⟨by rw [hst'm]; omega, by
                show N = (sint.Z st'.minRev).toNat; rw [hst'm]; simp⟩ (by rw [hst'm]; exact hNlt)
              $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf']
            · rw [← hst']; iframe; iframe #
            ihave Hwo : mvcc.watcherOwn key st' $$ [HminRev Hvict Hcomp Hrest0 Hchf]
            · rw [← hst']; iunfold mvcc.watcherOwn; simp only [fv]; iframe
            icases mvcc.sw_res_step γ σ v key r' .unsynced st' (evsw ++ B.evs, N)
              $$ [$Hst $Hwo $Hmem $Hmw] with ⟨Hst, Hmem⟩
            have hok' := Hl.ok.sync_step hvWu hvST .unsynced st' (evsw ++ B.evs, N)
              ⟨by rw [← hst']; exact fc, by rw [← hst']; exact fr, by rw [← hst'], by rw [← hst']; exact fv⟩
              (fun h => by cases h)
            unfold forMapPostcondition
            ileft
            isplitr
            · ipureintro; rfl
            iexists _
            iframe Hm
            iexists v.step key r' .unsynced st' (evsw ++ B.evs, N), PBv, Iris.Std.delete PBr key, key
            simp only [named]
            have e1 : (v.step key r' .unsynced st' (evsw ++ B.evs, N)).Ws = v.Ws := rfl
            have e2 : (v.step key r' .unsynced st' (evsw ++ B.evs, N)).Wu = v.Wu := rfl
            rw [e1, e2]
            iframe Hst Hmem Hsynced Hun Hvm Hbv Hrem Hwbm w s curRev compactionRev maxScanRev
              reachedCurRev victims wb
            ipureintro
            exact ⟨Hl.step Hkey r' .unsynced st' (evsw ++ B.evs, N) PBv _ hok' Hl.bv
              (fun k hk => by
                show (GMap.delete key PBr) !! k = _
                exact GMap.lookup_delete_ne _ (Ne.symm hk)), hm',
              mvcc.swc_step_Wu_sub _ v key r' .unsynced st' (evsw ++ B.evs, N) hsub⟩
          · -- reached: synced
            (try simp only [↓reduceIte, Bool.not_true])
            (try wp_auto)
            have hNC' : N = C.length := by have := hreached.1 hr; omega
            subst hNC'
            wp_apply (hAddG (mvcc.syncedAddr s) v.Ws key r' fcs) $$ [$Hsynced $Hfx] as Hsynced
            · ipureintro
              exact ⟨hvWs, by have := Hl.ok.ws_size; simp only [mvcc.SyncVars.st] at this; omega⟩
            (try wp_auto)
            wp_apply (hDelG (mvcc.unsyncedAddr s) v.Wu key r' fcs) $$ [$Hun $Hfx] as Hun
            (try wp_auto)
            ihave Hmw := mvcc.sw_memberRes_new_synced γ σ v key r' st' γw fcs (evsw ++ B.evs) C.length
              hM Hsr ⟨by rw [hst'm]; omega, by rw [hst'm]; exact Int.le_refl _⟩
              $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf']
            · rw [← hst']; iframe; iframe #
            ihave Hwo : mvcc.watcherOwn key st' $$ [HminRev Hvict Hcomp Hrest0 Hchf]
            · rw [← hst']; iunfold mvcc.watcherOwn; simp only [fv]; iframe
            icases mvcc.sw_res_step γ σ v key r' .synced st' (evsw ++ B.evs, C.length)
              $$ [$Hst $Hwo $Hmem $Hmw] with ⟨Hst, Hmem⟩
            have hok' := Hl.ok.sync_step hvWu hvST .synced st' (evsw ++ B.evs, C.length)
              ⟨by rw [← hst']; exact fc, by rw [← hst']; exact fr, by rw [← hst'], by rw [← hst']; exact fv⟩
              (fun _ γw' hM' => by
                rw [show σ.M !! key = some γw from hM] at hM'; cases hM'
                have := HpC.length_le
                simp only; omega)
            unfold forMapPostcondition
            iright; ileft
            isplitr
            · ipureintro; rfl
            iexists _
            iframe Hm
            iexists v.step key r' .synced st' (evsw ++ B.evs, C.length), PBv, Iris.Std.delete PBr key, key
            simp only [named]
            have e1 : (v.step key r' .synced st' (evsw ++ B.evs, C.length)).Ws = <[key := r']> v.Ws := rfl
            have e2 : (v.step key r' .synced st' (evsw ++ B.evs, C.length)).Wu = GMap.delete key v.Wu := rfl
            rw [e1, e2]
            iframe Hst Hmem Hsynced Hun Hvm Hbv Hrem Hwbm w s curRev compactionRev maxScanRev
              reachedCurRev victims wb
            ipureintro
            exact ⟨Hl.step Hkey r' .synced st' (evsw ++ B.evs, C.length) PBv _ hok' Hl.bv
              (fun k hk => by
                show (GMap.delete key PBr) !! k = _
                exact GMap.lookup_delete_ne _ (Ne.symm hk)), hm',
              mvcc.swc_step_Wu_sub _ v key r' .synced st' (evsw ++ B.evs, C.length) hsub⟩
      · -- the events below the first revision left out
        have hMlen : M < 2 ^ 63 := by omega
        have hMz : sint.Z (W64 (M : Int)) = M := by word
        have hMne : ¬ B.moreRev = W64 0 := by
          rw [hmrM]; intro h
          have := congrArg (fun x : w64 => sint.Z x) h
          simp only [hMz] at this
          rw [show sint.Z (W64 0 : w64) = 0 by decide] at this; omega
        rw [decide_eq_false hMne]
        wp_auto
        have hmD : sint.nat st.minRev ≤ M := by omega
        ihave #Hwf' := mvcc.sw_evsWf_extend γ r' γw.lo evsw (sint.nat st.minRev) M C hmD
          (by omega) hloN $$ [$Hwf $HcertQ $HokQ]
        rw [← hevB]
        have hmodB := mvcc.watchEvents_modRev C HCwf.2.1 r' (sint.nat st.minRev) M
          (by omega)
        rw [← hevB] at hmodB
        wp_apply (hSend γ key γw r' fcs st.ch 1 (1 : Qp).half evsw M _ eps B.evs (DFrac.own 1))
          $$ [Hchf Hlv Ha Hsl] as %b ⟨Hchf, Hlv, Hsl, Ha⟩
        · rw [if_neg hBne]
          iframe Hmeta Hfx Hfo Hch Hchf Hlv Ha Hwf' Hsl HevB
          isplitr
          · ileft; ipureintro; rfl
          ipureintro
          refine ⟨Heplen, rfl, fun _ => rfl, fun ev hev => ?_, fun _ ev hev => ?_⟩
          · have := hmodB ev hev; rw [hcur]; omega
          · have := hmodB ev hev; omega
        rw [if_neg hBne]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          wp_auto
          wp_apply wp_mapInsert $$ Hvm as Hvm
          (try wp_auto)
          wp_apply (hDelG (mvcc.unsyncedAddr s) v.Wu key r' fcs) $$ [$Hun $Hfx] as Hun
          (try wp_auto)
          generalize hst' : ({ st with minRev := B.moreRev, victim := true } :
            mvcc.WatcherSt) = st'
          have hst'm : sint.Z st'.minRev = M := by rw [← hst']; simp only; rw [hmrM]; exact hMz
          ihave Hmw := mvcc.sw_memberRes_new_victim γ σ v key r' B st' γw fcs evsw M
            hM Hsr hvWs fvo ⟨by rw [hst'm]; omega, by
              show M = (sint.Z st'.minRev).toNat; rw [hst'm]; simp,
              fun _ => by rw [← hst'], fun ev hev => by
                have := hmodB ev hev
                rw [hst'm]; omega⟩
            $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf']
          · rw [← hst']; iframe; iframe #
          ihave Hwo : mvcc.watcherOwn key st' $$ [HminRev Hvict Hcomp Hrest0 Hchf]
          · rw [← hst']; iunfold mvcc.watcherOwn; iframe
          icases mvcc.sw_res_step γ σ v key r' (.victim B) st' (evsw, M)
            $$ [$Hst $Hwo $Hmem $Hmw] with ⟨Hst, Hmem⟩
          have hok' := Hl.ok.sync_step hvWu hvST (.victim B) st' (evsw, M)
            ⟨by rw [← hst']; exact fc, by rw [← hst']; exact fr, by rw [← hst'], by rw [← hst']; rfl⟩
            (fun h => by cases h)
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists _
          iframe Hm
          iexists v.step key r' (.victim B) st' (evsw, M), <[key := (ebp, B)]> PBv,
            Iris.Std.delete PBr key, key
          simp only [named]
          have e1 : (v.step key r' (.victim B) st' (evsw, M)).Ws = v.Ws := rfl
          have e2 : (v.step key r' (.victim B) st' (evsw, M)).Wu = GMap.delete key v.Wu := rfl
          rw [e1, e2, GMap.fmap_insert]
          iframe Hst Hmem Hsynced Hun Hvm Hrem Hwbm w s curRev compactionRev maxScanRev
            reachedCurRev victims wb
          isplitl [Hbv Heb Hsl Hcap]
          · iapply (BigSepM.bigSepM_insert (by rw [gmap_get?_eq]; exact hPBv0)).2
            iframe Hbv
            isplitr
            · ipureintro; exact Hebnn
            iunfold mvcc.ownEventBatch
            iexists sl, eps
            iframe Heb Hsl Hcap HevB
            ipureintro; exact Heplen
          ipureintro
          exact ⟨Hl.step Hkey r' (.victim B) st' (evsw, M) _ _ hok'
            (by show <[key := B]> v.Bv = _; rw [Hl.bv, GMap.fmap_insert])
            (fun k hk => by
              show (GMap.delete key PBr) !! k = _
              exact GMap.lookup_delete_ne _ (Ne.symm hk)), hm',
            mvcc.swc_step_Wu_sub _ v key r' (.victim B) st' (evsw, M) hsub⟩
        · simp only [↓reduceIte]
          wp_auto
          wp_apply HgPA
          (try wp_auto)
          rw [fv]
          wp_auto
          rw [decide_eq_false hMne]
          wp_auto
          generalize hst' : ({ st with minRev := B.moreRev } : mvcc.WatcherSt) = st'
          have hst'm : sint.Z st'.minRev = M := by rw [← hst']; simp only; rw [hmrM]; exact hMz
          ihave Hmw := mvcc.sw_memberRes_new_unsynced γ σ v key r' st' γw fcs (evsw ++ B.evs) M C
            hM Hsr hvWs hvWu ⟨by rw [hst'm]; omega, by
              show M = (sint.Z st'.minRev).toNat; rw [hst'm]; simp⟩ (by rw [hst'm]; omega)
            $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf']
          · rw [← hst']; iframe; iframe #
          ihave Hwo : mvcc.watcherOwn key st' $$ [HminRev Hvict Hcomp Hrest0 Hchf]
          · rw [← hst']; iunfold mvcc.watcherOwn; simp only [fv]; iframe
          icases mvcc.sw_res_step γ σ v key r' .unsynced st' (evsw ++ B.evs, M)
            $$ [$Hst $Hwo $Hmem $Hmw] with ⟨Hst, Hmem⟩
          have hok' := Hl.ok.sync_step hvWu hvST .unsynced st' (evsw ++ B.evs, M)
            ⟨by rw [← hst']; exact fc, by rw [← hst']; exact fr, by rw [← hst'], by rw [← hst']; exact fv⟩
            (fun h => by cases h)
          unfold forMapPostcondition
          ileft
          isplitr
          · ipureintro; rfl
          iexists _
          iframe Hm
          iexists v.step key r' .unsynced st' (evsw ++ B.evs, M), PBv, Iris.Std.delete PBr key, key
          simp only [named]
          have e1 : (v.step key r' .unsynced st' (evsw ++ B.evs, M)).Ws = v.Ws := rfl
          have e2 : (v.step key r' .unsynced st' (evsw ++ B.evs, M)).Wu = v.Wu := rfl
          rw [e1, e2]
          iframe Hst Hmem Hsynced Hun Hvm Hbv Hrem Hwbm w s curRev compactionRev maxScanRev
            reachedCurRev victims wb
          ipureintro
          exact ⟨Hl.step Hkey r' .unsynced st' (evsw ++ B.evs, M) PBv _ hok' Hl.bv
            (fun k hk => by
              show (GMap.delete key PBr) !! k = _
              exact GMap.lookup_delete_ne _ (Ne.symm hk)), hm',
            mvcc.swc_step_Wu_sub _ v key r' .unsynced st' (evsw ++ B.evs, M) hsub⟩
  isplitr
  · imodintro
    iintro %i %key %m' ⟨%Hkey, %Hu⟩ HP
    iNamed HP
    exfalso
    obtain ⟨Hl, hm', -⟩ := Hi
    have hW : (W' !! key).isSome := by
      have := (Hkset key).1 (List.mem_of_getElem? Hkey)
      rw [GMap.domSet, GMap.lookup_fmap] at this; simpa using this
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hW
    subst hm'
    simp only [GMap.domSet, GMap.lookup_fmap, hr] at Hu
    cases Hu
  iintro %m' HP Hm
  iNamed HP
  obtain ⟨Hl, hm', hsub⟩ := Hi
  wp_auto
  wp_apply +noauto (hAddV s st γ σ.vs σ.vbs vm (DFrac.own 1) (GMap.fmap Prod.fst PBv))
    $$ [$HwsAll $Hvf $Hvs $Hvcap $Hvm] as ⟨Hvm, %vs', Hvf, Hvs, Hvcap⟩
  have hsz : (GMap.fmap Prod.fst PBv).size = v.Bv.size := by
    rw [Hl.bv, GMap.map_size_fmap, GMap.map_size_fmap]
  rw [hsz]
  ihave Hvbs : [∗list] x ∈ (if v.Bv.size = 0 then σ.vbs else σ.vbs ++ [vm]).zip
      (if v.Bv.size = 0 then σ.VB else σ.VB ++ [v.Bv]), mvcc.ownWatcherBatch x.1 x.2 $$
      [Hvbs Hvm Hbv]
  · by_cases h0 : v.Bv.size = 0
    · simp only [h0, ↓reduceIte]; iexact Hvbs
    · simp only [h0, ↓reduceIte]
      rw [List.zip_append Hvlen]
      iapply BigSepL.bigSepL_append.2
      iframe Hvbs
      simp only [List.zip_cons_cons, List.zip_nil_right]
      iapply BigSepL.bigSepL_singleton.2
      iunfold mvcc.ownWatcherBatch
      iexists PBv
      iframe Hvm Hbv
      ipureintro; exact Hl.bv
  have hlen' : (if v.Bv.size = 0 then σ.vbs else σ.vbs ++ [vm]).length =
      (if v.Bv.size = 0 then σ.VB else σ.VB ++ [v.Bv]).length := by
    split <;> simp [Hvlen]
  -- the lock's state after
  let σf : mvcc.WsState := mvcc.WsState.mk σ.Lmu v.Ws v.Wu v.ST σ.Wo σ.M v.E vs'
    (if v.Bv.size = 0 then σ.vbs else σ.vbs ++ [vm])
    (if v.Bv.size = 0 then σ.VB else σ.VB ++ [v.Bv])
  have hvo : ∀ k, σf.victimOf k = (v.st σ).victimOf k := by
    intro k
    rw [mvcc.SyncVars.st_victimOf]
    by_cases h0 : v.Bv.size = 0
    · have hBv : v.Bv = ∅ := GMap.map_size_empty_inv _ h0
      rw [hBv]
      show (if v.Bv.size = 0 then σ.VB else σ.VB ++ [v.Bv]).findSome? _ = _
      rw [if_pos h0]; simp; rfl
    · show (if v.Bv.size = 0 then σ.VB else σ.VB ++ [v.Bv]).findSome? _ = _
      rw [if_neg h0, List.findSome?_append]; simp; rfl
  have hokf : mvcc.WsOk σf := by
    by_cases h0 : v.Bv.size = 0
    · have hBv : v.Bv = ∅ := GMap.map_size_empty_inv _ h0
      exact Hl.ok.sync_final_empty hBv σf rfl rfl rfl rfl rfl rfl rfl
        (show (if v.Bv.size = 0 then σ.VB else σ.VB ++ [v.Bv]) = σ.VB by rw [if_pos h0])
    · refine Hl.ok.congr rfl rfl rfl rfl rfl rfl rfl hvo ?_
      have : σf.VB = (v.st σ).VB := by
        show (if v.Bv.size = 0 then σ.VB else σ.VB ++ [v.Bv]) = σ.VB ++ [v.Bv]; rw [if_neg h0]
      rw [this]; exact Hl.ok.v_one
  imod ghostVar_update σf γ.wst σ $$ Hσ with Hσ
  (try wp_auto)
  ihave HPf : mvcc.watchStoreBody s γ 1 σf $$ [Hσ Hwlog Hsynced Hun Hvf Hvs Hvcap Hvbs Hst Hwo
      Hmeta Hwt Hmem]
  · iunfold mvcc.watchStoreBody
    simp only [named]
    iframe Hσ Hwlog Hcert Hsynced Hun Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmfix
    isplitr
    · ipureintro; exact hlen'
    isplitl [Hmem]
    · iapply (BigSepM.bigSepM_mono (fun {k x} _ => ?_)) $$ Hmem
      rw [mvcc.sw_memberRes_congr γ 1 (v.st σ) σf k x rfl rfl rfl rfl (hvo k).symm]
    isplitr
    · iapply (BigSepM.bigSepM_mono (fun {k x} _ => by unfold mvcc.outRes; exact .rfl)) $$ Hout
    ipureintro; exact hokf
  iapply HΦ
  iexists σf
  iframe HrtR HbucketQ HlogQ HPf
  ipureintro
  refine ⟨hsub, fun w hw => ?_⟩
  have hnk : w ∉ keys.take keys.length := by
    rw [List.take_length]; intro hm
    have := (Hkset w).1 hm
    rw [GMap.domSet, GMap.lookup_fmap, hw] at this; cases this
  obtain ⟨h1, h2, -⟩ := Hl.rest w hnk
  exact ⟨h2, h1⟩

end proof

end EtcdGrove
end Perennial
