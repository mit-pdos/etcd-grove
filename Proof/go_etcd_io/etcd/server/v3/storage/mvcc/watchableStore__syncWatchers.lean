/-
Proof of `Spec/.../mvcc/watchableStore__syncWatchers.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__syncWatchers
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__size
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__choose
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
theorem mvcc.sw_wp_max_int64 (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.int64, go.int64])) (Val #x)) (Val #y))
    {{ RET #(if sint.Z y < sint.Z x then x else y); True }} := by
  wp_start
  by_cases h : sint.Z y < sint.Z x
  · rw [decide_eq_true h, if_pos h]; wp_auto; iapply HΦ; itrivial
  · rw [decide_eq_false h, if_neg h]; wp_auto; iapply HΦ; itrivial

/-- `s.unsynced.delete(w)` while the loop ranges over the chosen group's set: the unsynced group
itself (`self`, its set lent to the loop: the map stays the group's) or another group. -/
theorem mvcc.sw_wp_unsynced_delete (hDel : mvcc.watcherGroup.delete.spec (GF := GF) (hG := hG))
    (self : Bool) (s : Loc) (ws : GoMap) (Wu W' : GMap Loc mvcc.WatchRange) (m' : GMap Loc Unit)
    (key : Loc) (r : mvcc.WatchRange) (fcs : GoSlice)
    (hm' : m' = if self then domSet Wu else domSet W') :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        (if self then (mvcc.ownWatcherSet ws (domSet Wu) -∗
          mvcc.ownWatcherGroupAt (mvcc.unsyncedAddr s) Wu ws)
        else mvcc.ownWatcherGroup (mvcc.unsyncedAddr s) Wu) ∗ ws ↦$ m' ∗ mvcc.watcherFixed key r fcs }}
      (App (Val (mvcc.unsyncedAddr s @!! go.GoType.PointerType watcherGroup.ty @!! go!"delete"))
        (Val #key))
    {{ (b : Bool), RET #b;
        (if self then (mvcc.ownWatcherSet ws (domSet (GMap.delete key Wu)) -∗
          mvcc.ownWatcherGroupAt (mvcc.unsyncedAddr s) (GMap.delete key Wu) ws)
        else mvcc.ownWatcherGroup (mvcc.unsyncedAddr s) (GMap.delete key Wu)) ∗
        ws ↦$ (if self then domSet (GMap.delete key Wu) else domSet W') }} := by
  iintro %Φ ⟨#Hpkg, Hun, Hm, #Hf⟩ HΦ
  cases self
  · simp only [Bool.false_eq_true, ↓reduceIte] at hm' ⊢
    iapply (mvcc.watcherGroup.delete.spec_group hDel (mvcc.unsyncedAddr s) Wu key r fcs) $$ [Hun] [Hm HΦ]
    · iframe Hpkg Hun Hf
    inext
    iintro Hun
    iapply HΦ
    iframe Hun
    rw [← hm']; iexact Hm
  · simp only [↓reduceIte] at hm' ⊢
    subst hm'
    ihave Hg := Hun $$ [Hm]
    · iunfold mvcc.ownWatcherSet; iexact Hm
    iapply (hDel (mvcc.unsyncedAddr s) Wu ws key r fcs) $$ [Hg] [HΦ]
    · iframe Hpkg Hg Hf
    inext
    iintro Hg
    icases mvcc.ownWatcherGroupAt_set _ _ _ _ $$ Hg with ⟨Hs, Hw⟩
    iapply HΦ
    iframe Hw
    iunfold mvcc.ownWatcherSet at Hs; iexact Hs

set_option maxRecDepth 20000 in
theorem mvcc.watchableStore.syncWatchers.wp_proof
    (hSize : mvcc.watcherGroup.size.spec (GF := GF) (hG := hG))
    (hChoose : mvcc.watcherGroup.choose.spec (GF := GF) (hG := hG))
    (hRange : mvcc.rangeEvents.spec (GF := GF) (hG := hG))
    (hNWB : mvcc.newWatcherBatch.spec (GF := GF) (hG := hG))
    (hSend : mvcc.watcher.send.spec (GF := GF) (hG := hG))
    (hAdd : mvcc.watcherGroup.add.spec (GF := GF) (hG := hG))
    (hDel : mvcc.watcherGroup.delete.spec (GF := GF) (hG := hG))
    (hAddV : mvcc.watchableStore.addVictim.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.syncWatchers.spec (GF := GF) (hG := hG) := by
  have hAddG := mvcc.watcherGroup.add.spec_group hAdd
  intro s st γ
  wp_start as ⟨#Hws, HR⟩
  ihave #HwsAll : mvcc.isWatchableStore s st γ $$ []
  · iexact Hws
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%gS, #HgS, #HgSS⟩,
    ⟨%gP, #HgP, #HgPS⟩, -, #HmaxW, -, ⟨%gS', #HgS', #HgSet⟩⟩
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
  icases HQ with ⟨%C, %ntok, HQ⟩
  iNamedSuffix HQ "Q"
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
        (self = true → g = mvcc.unsyncedAddr s ∧ W' = σ.Wu)⌝ ∗
      mvcc.ownWatcherGroup g W' ∗
      (if self then iprop(True) else mvcc.ownWatcherGroup (mvcc.unsyncedAddr s) σ.Wu) $$ [Hch]
  · icases Hch with (⟨%H1, Hg, %Hm⟩ | ⟨%W', %H2, Hun, Hg, %Hm⟩)
    · iexists true, σ.Wu
      obtain ⟨rfl, -⟩ := H1
      iframe Hg
      isplitr
      · ipureintro
        refine ⟨GMap.map_subseteq_refl _, hne_of _ (fun h => Hif (by rw [h]; rfl)), Hm,
          fun _ => ⟨rfl, rfl⟩⟩
      simp only [↓reduceIte]
      itrivial
    · iexists false, W'
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hg Hun
      ipureintro
      refine ⟨H2.1, hne_of _ ?_, Hm, fun h => by cases h⟩
      have := H2.2.2
      have h512 : sint.Z (W64 512 : w64) = 512 := by decide
      rw [h512] at this
      omega
  icases Hch with ⟨%self, %W', %HW', Hg, Hun⟩
  obtain ⟨hW'sub, hW'ne, hminR, hself⟩ := HW'
  have hW'Wu : ∀ w r, W' !! w = some r → σ.Wu !! w = some r := fun w r h => hW'sub w r h
  have hW'ST : ∀ w, (W' !! w).isSome → ∃ st, STu !! w = some st ∧ σ.ST !! w = some st := by
    intro w hw
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hw
    have hu : (σ.Wu !! w).isSome := by rw [hW'Wu w r hr]; rfl
    obtain ⟨st, hst⟩ := Option.isSome_iff_exists.1 (Hok.live_st w (Or.inr (Or.inl hu)))
    exact ⟨st, by rw [hSTu, if_pos hu]; exact hst, hst⟩
  obtain ⟨hm0, hm1, hm2⟩ := mvcc.sw_minRevOf_bounds STu (domSet W') ((C.length : Int) - 1)
    (by obtain ⟨w, hw⟩ := hW'ne; exact ⟨w, by rw [GMap.domSet, GMap.lookup_fmap]; simpa using hw⟩)
    (fun w hw => by
      have hw' : (W' !! w).isSome := by rw [GMap.domSet, GMap.lookup_fmap] at hw; simpa using hw
      obtain ⟨st, h1, -⟩ := hW'ST w hw'; rw [h1]; rfl)
    (fun w st hw hs => by
      have hw' : (W' !! w).isSome := by rw [GMap.domSet, GMap.lookup_fmap] at hw; simpa using hw
      obtain ⟨st', h1, h2⟩ := hW'ST w hw'
      obtain rfl : st' = st := Option.some.inj (h1.symm.trans hs)
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hw'
      have := Hbd w st' h2 (by rw [hW'Wu w r hr]; rfl)
      omega)
  rw [← hminR] at hm0 hm1 hm2
  ihave %HCwf : ⌜mvcc.LogWf' C ∧ C.length < 2 ^ 63 ∧ ∀ cs ∈ C, cs.length < 2 ^ 63⌝ $$ [HcertQ]
  · iunfold mvcc.idxCert at HcertQ
    icases HcertQ with ⟨-, -, %H, -⟩
    ipureintro; exact H
  have hcur1 : sint.Z (W64 ((C.length : Int) - 1) + W64 1) = (C.length : Int) := by word
  wp_apply (hRange _ _ γ.st _ _ _ _ C minRev (W64 ((C.length : Int) - 1) + W64 1) g W')
    $$ [$HbkS $HrtR $HbucketQ $HcertQ $Hg] as %evs ⟨HrtR, HbucketQ, Hg, %ps, Hevs, Hevcap, %Hpslen,
      #HevIs⟩
  · ipureintro; rw [hcur1]; omega
  have hnat1 : sint.nat (W64 ((C.length : Int) - 1) + W64 1) = C.length := by
    show (sint.Z _).toNat = _; rw [hcur1]; simp
  rw [hnat1] at Hpslen ⊢
  generalize hevm : (mvcc.logEvents C (sint.nat minRev) C.length).filter
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
  -- the chosen group's set, lent to the loop
  icases (mvcc.ownWatcherGroup_at g W' 1).1 $$ Hg with ⟨%ws, Hg⟩
  iunfold mvcc.ownWatcherGroupAt at Hg
  icases Hg with ⟨%km, %t, %KM, %L, Hg⟩
  iNamed Hg
  wp_auto
  ihave Hrest : mvcc.ownWatcherSet ws (domSet W') -∗ mvcc.ownWatcherGroupAt g W' ws $$
      [Hwg Hkm Hivt Hranges]
  · iintro Hws
    iapply mvcc.ownWatcherGroupAt_intro g W' km ws t KM L HL
    iframe
    iframe #
  ihave Hun : (if self then (mvcc.ownWatcherSet ws (domSet σ.Wu) -∗
      mvcc.ownWatcherGroupAt (mvcc.unsyncedAddr s) σ.Wu ws)
      else mvcc.ownWatcherGroup (mvcc.unsyncedAddr s) σ.Wu) $$ [Hun Hrest]
  · cases hs : self
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at *; iexact Hun
    · obtain ⟨rfl, rfl⟩ := hself hs
      simp only [↓reduceIte]
      iexact Hrest
  iunfold mvcc.ownWatcherSet at Hws
  iunfold mvcc.ownWatcherBatch at Hwb
  icases Hwb with ⟨%PB, Hwbm, %HBt, Hbs⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range_gen (K := Loc) (V := Unit)
    (fun (keys : List Loc) (i : Nat) (m' : GMap Loc Unit) => iprop(
      ∃ (v : mvcc.SyncVars) (PBv PBr : GMap Loc (Loc × mvcc.EventBatch)) (wv : Loc),
      "Hst" ∷ ([∗map] w ↦ x ∈ v.ST, mvcc.watcherOwn w x) ∗
      "Hmem" ∷ ([∗map] w ↦ x ∈ v.ST, mvcc.memberRes γ 1 (v.st σ) w x) ∗
      "Hsynced" ∷ mvcc.ownWatcherGroup (mvcc.syncedAddr s) v.Ws ∗
      "Hun" ∷ (if self then (mvcc.ownWatcherSet ws (domSet v.Wu) -∗
          mvcc.ownWatcherGroupAt (mvcc.unsyncedAddr s) v.Wu ws)
        else mvcc.ownWatcherGroup (mvcc.unsyncedAddr s) v.Wu) ∗
      "Hvm" ∷ vm ↦$ GMap.fmap Prod.fst PBv ∗
      "Hbv" ∷ ([∗map] _w ↦ p ∈ PBv, ⌜p.1 ≠ null⌝ ∗ mvcc.ownEventBatch p.1 p.2) ∗
      "Hrem" ∷ ([∗map] _w ↦ p ∈ PBr, ⌜p.1 ≠ null⌝ ∗ mvcc.ownEventBatch p.1 p.2) ∗
      "Hwbm" ∷ wb ↦$ GMap.fmap Prod.fst PB ∗
      "w" ∷ w_ptr ↦ wv ∗ "s" ∷ s_ptr ↦ s ∗
      "curRev" ∷ curRev_ptr ↦ W64 ((C.length : Int) - 1) ∗
      "compactionRev" ∷ compactionRev_ptr ↦ W64 (-1) ∗
      "victims" ∷ victims_ptr ↦ vm ∗ "wb" ∷ wb_ptr ↦ wb ∗
      "%Hi" ∷ ⌜mvcc.SyncLoop σ v PB PBv PBr keys i ∧
        m' = (if self then domSet v.Wu else domSet W')⌝))
    _ _ _ ws (domSet W') (DFrac.own 1)) $$ Hws
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hst Hmem Hsynced Hun Hvm Hbs Hwbm w s curRev compactionRev victims wb]
  · iexists mvcc.SyncVars.init σ, ∅, PB, zero_val Loc
    simp only [named, GMap.fmap_empty]
    have hI : ∀ k, (mvcc.SyncVars.st σ (mvcc.SyncVars.init σ)).victimOf k = σ.victimOf k := by
      intro k; rw [mvcc.SyncVars.st_victimOf]; simp [mvcc.SyncVars.init]
    iframe Hvm Hwbm w s curRev compactionRev victims wb Hbs
    have e1 : (mvcc.SyncVars.init σ).ST = σ.ST := rfl
    have e2 : (mvcc.SyncVars.init σ).Ws = σ.Ws := rfl
    have e3 : (mvcc.SyncVars.init σ).Wu = σ.Wu := rfl
    rw [e1, e2, e3]
    iframe Hst Hsynced Hun
    isplitl [Hmem]
    · iapply (BigSepM.bigSepM_mono (fun {k x} _ => ?_)) $$ Hmem
      rw [mvcc.sw_memberRes_congr γ 1 (mvcc.SyncVars.st σ (mvcc.SyncVars.init σ)) σ k x
        rfl rfl rfl rfl (hI k)]
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    ipureintro
    refine ⟨⟨Hok.sync_init, by rw [GMap.fmap_empty]; rfl, fun k _ => by
      simp [mvcc.SyncVars.init]⟩, ?_⟩
    cases hs : self
    · rfl
    · obtain ⟨-, rfl⟩ := hself hs; rfl
  isplitr
  · imodintro
    iintro %i %key %u %m' ⟨%Hkey, %Hu⟩ HP Hm
    iNamed HP
    obtain ⟨Hl, hm'⟩ := Hi
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
    wp_apply mvcc.sw_wp_max_int64
    rw [if_pos (show sint.Z st.minRev < sint.Z (W64 ((C.length : Int) - 1) + W64 1) by
      rw [hcur1]; omega)]
    (try wp_auto)
    wp_apply wp_map_lookup2 $$ Hwbm as Hwbm
    have hbk : GMap.fmap Prod.snd PB !! key = mvcc.memberBatch r' st evm := by
      rw [← HBt, mvcc.batchOf_lookup, hr, hSTuk]
    have hmb := mvcc.memberBatch_logEvents C HCwf.1 HCwf.2.1 HCwf.2.2 r' st
      (fun ev => mvcc.wgCovers W' ev.kv.key) (sint.nat minRev) C.length
      (fun ev hc => by
        simp only [mvcc.wgCovers, decide_eq_true_eq]; exact ⟨key, r', hr, hc⟩)
      (by
        have := hm2 key st (by rw [GMap.domSet, GMap.lookup_fmap, hr]; rfl) hSTuk
        show ((sint.Z minRev).toNat : Int) ≤ _; omega)
      (Nat.le_refl _)
    rw [hevm] at hmb
    rcases hmb with ⟨hnone, hwE⟩ | ⟨B, hsome, hBne, hBev⟩
    · -- no batch: synced
      rw [hnone, GMap.lookup_fmap] at hbk
      have hPBk : PB !! key = none := by
        cases h : PB !! key with
        | none => rfl
        | some _ => rw [h] at hbk; cases hbk
      rw [hPBk]
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, decide_false,
        Bool.not_false]
      wp_auto
      wp_apply (hAddG (mvcc.syncedAddr s) v.Ws key r' fcs) $$ [$Hsynced $Hfx] as Hsynced
      · ipureintro; exact ⟨hvWs, by have := Hl.ok.ws_size; simp only [mvcc.SyncVars.st] at this; omega⟩
      (try wp_auto)
      wp_apply (mvcc.sw_wp_unsynced_delete hDel self s ws v.Wu W' m' key r' fcs hm')
        $$ [$Hun $Hm $Hfx] as %b ⟨Hun, Hm⟩
      (try wp_auto)
      obtain ⟨fc, fr, fv, fch, fvo, fbv, -⟩ := Hl.unsynced_facts hvWu hvST
      have hmN : sint.nat st.minRev ≤ C.length := by
        show (sint.Z st.minRev).toNat ≤ _; omega
      have hloN : γw.lo ≤ sint.nat st.minRev := by
        show _ ≤ (sint.Z st.minRev).toNat; omega
      ihave #Hwf' := mvcc.sw_evsWf_extend γ r' γw.lo evsw (sint.nat st.minRev) C.length C hmN
        (Nat.le_refl _) hloN $$ [$Hwf $HcertQ]
      rw [hwE, List.append_nil] at *
      generalize hst' : ({ st with minRev := W64 ((C.length : Int) - 1) + W64 1 } : mvcc.WatcherSt) = st'
      have hst'm : sint.Z st'.minRev = C.length := by rw [← hst']; exact hcur1
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
      iframe Hst Hmem Hsynced Hun Hvm Hbv Hrem Hwbm w s curRev compactionRev victims wb
      ipureintro
      refine ⟨Hl.step Hkey r' .synced st' (evsw, C.length) PBv PBr hok' Hl.bv (fun _ _ => rfl), ?_⟩
      cases self <;> rfl
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
      obtain ⟨fc, fr, fv, fch, fvo, fbv, -⟩ := Hl.unsynced_facts hvWu hvST
      have hmN : sint.nat st.minRev ≤ C.length := by
        show (sint.Z st.minRev).toNat ≤ _; omega
      have hloN : γw.lo ≤ sint.nat st.minRev := by
        show _ ≤ (sint.Z st.minRev).toNat; omega
      ihave #Hfx0 := Hfx
      iunfold mvcc.watcherFixed at Hfx0
      icases Hfx0 with ⟨%Hwnn, %ks, %es', #Hk, #Hks, #He, #Hes, #Hsr', #Hid, #Hfcs⟩
      iunfold gaugeSpec at HgPS
      icases HgPS with ⟨-, -, #HgPA⟩
      have hvicB : (σ.victimOf key) = none := fvo
      (try wp_auto)
      rcases hBev with ⟨hmr0, hevB⟩ | ⟨M, hmrM, hMm, hMC, hevB⟩
      · -- all of the range's events
        rw [decide_eq_true hmr0]
        wp_auto
        have hmD : sint.nat st.minRev ≤ C.length := hmN
        ihave #Hwf' := mvcc.sw_evsWf_extend γ r' γw.lo evsw (sint.nat st.minRev) C.length C hmD
          (Nat.le_refl _) hloN $$ [$Hwf $HcertQ]
        rw [← hevB]
        have hmodB := mvcc.watchEvents_modRev C HCwf.2.1 r' (sint.nat st.minRev) C.length
          (Nat.le_refl _)
        rw [← hevB] at hmodB
        wp_apply (hSend γ key γw r' fcs st.ch 1 (1 : Qp).half evsw C.length _ eps B.evs (DFrac.own 1))
          $$ [Hchf Hlv Ha Hsl] as %b ⟨Hchf, Hlv, Hsl, Ha⟩
        · rw [if_neg hBne]
          iframe Hmeta Hfx Hfo Hch Hchf Hlv Ha Hwf' Hsl HevB
          ipureintro
          refine ⟨Heplen, rfl, fun _ => rfl, fun ev hev => ?_, fun _ ev hev => ?_⟩
          · have := hmodB ev hev; rw [hcur]; omega
          · have := hmodB ev hev
            have : (sint.nat st.minRev : Int) = sint.Z st.minRev := by
              show ((sint.Z st.minRev).toNat : Int) = _; omega
            omega
        rw [if_neg hBne]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          wp_auto
          wp_apply wp_mapInsert $$ Hvm as Hvm
          (try wp_auto)
          wp_apply (mvcc.sw_wp_unsynced_delete hDel self s ws v.Wu W' m' key r' fcs hm')
            $$ [$Hun $Hm $Hfx] as %b ⟨Hun, Hm⟩
          (try wp_auto)
          generalize hst' : ({ st with minRev := W64 ((C.length : Int) - 1) + W64 1, victim := true } :
            mvcc.WatcherSt) = st'
          have hst'm : sint.Z st'.minRev = C.length := by rw [← hst']; exact hcur1
          have hPBv0 : PBv !! key = none := by
            have := fbv; rw [Hl.bv, GMap.lookup_fmap] at this
            cases h : PBv !! key with
            | none => rfl
            | some _ => rw [h] at this; cases this
          ihave Hmw := mvcc.sw_memberRes_new_victim γ σ v key r' B st' γw fcs evsw C.length
            hM Hsr hvWs fvo ⟨by rw [hst'm]; omega, by
              show C.length = (sint.Z st'.minRev).toNat; rw [hst'm]; simp,
              fun h => absurd hmr0 h, fun ev hev => by
                have := hmodB ev hev
                have : (sint.nat st.minRev : Int) = sint.Z st.minRev := by
                  show ((sint.Z st.minRev).toNat : Int) = _; omega
                rw [hst'm]; omega⟩
            $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf']
          · rw [← hst']; iframe; iframe #
          ihave Hwo : mvcc.watcherOwn key st' $$ [HminRev Hvict Hcomp Hrest0 Hchf]
          · rw [← hst']; iunfold mvcc.watcherOwn; iframe
          icases mvcc.sw_res_step γ σ v key r' (.victim B) st' (evsw, C.length)
            $$ [$Hst $Hwo $Hmem $Hmw] with ⟨Hst, Hmem⟩
          have hok' := Hl.ok.sync_step hvWu hvST (.victim B) st' (evsw, C.length)
            ⟨by rw [← hst']; exact fc, by rw [← hst']; exact fr, by rw [← hst'], by rw [← hst']; rfl⟩
            (fun h => by cases h)
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists _
          iframe Hm
          iexists v.step key r' (.victim B) st' (evsw, C.length), <[key := (ebp, B)]> PBv,
            Iris.Std.delete PBr key, key
          simp only [named]
          have e1 : (v.step key r' (.victim B) st' (evsw, C.length)).Ws = v.Ws := rfl
          have e2 : (v.step key r' (.victim B) st' (evsw, C.length)).Wu = GMap.delete key v.Wu := rfl
          rw [e1, e2, GMap.fmap_insert]
          iframe Hst Hmem Hsynced Hun Hvm Hrem Hwbm w s curRev compactionRev victims wb
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
          refine ⟨Hl.step Hkey r' (.victim B) st' (evsw, C.length) _ _ hok'
            (by show <[key := B]> v.Bv = _; rw [Hl.bv, GMap.fmap_insert])
            (fun k hk => by
              show (GMap.delete key PBr) !! k = _
              exact GMap.lookup_delete_ne _ (Ne.symm hk)), ?_⟩
          cases self <;> rfl
        · simp only [↓reduceIte]
          wp_auto
          wp_apply HgPA
          (try wp_auto)
          rw [fv]
          wp_auto
          rw [decide_eq_true hmr0]
          wp_auto
          wp_apply (hAddG (mvcc.syncedAddr s) v.Ws key r' fcs) $$ [$Hsynced $Hfx] as Hsynced
          · ipureintro
            exact ⟨hvWs, by have := Hl.ok.ws_size; simp only [mvcc.SyncVars.st] at this; omega⟩
          (try wp_auto)
          wp_apply (mvcc.sw_wp_unsynced_delete hDel self s ws v.Wu W' m' key r' fcs hm')
            $$ [$Hun $Hm $Hfx] as %b ⟨Hun, Hm⟩
          (try wp_auto)
          generalize hst' : ({ st with minRev := W64 ((C.length : Int) - 1) + W64 1 } : mvcc.WatcherSt) = st'
          have hst'm : sint.Z st'.minRev = C.length := by rw [← hst']; exact hcur1
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
          iframe Hst Hmem Hsynced Hun Hvm Hbv Hrem Hwbm w s curRev compactionRev victims wb
          ipureintro
          refine ⟨Hl.step Hkey r' .synced st' (evsw ++ B.evs, C.length) PBv _ hok' Hl.bv
            (fun k hk => by
              show (GMap.delete key PBr) !! k = _
              exact GMap.lookup_delete_ne _ (Ne.symm hk)), ?_⟩
          cases self <;> rfl
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
          (by omega) hloN $$ [$Hwf $HcertQ]
        rw [← hevB]
        have hmodB := mvcc.watchEvents_modRev C HCwf.2.1 r' (sint.nat st.minRev) M
          (by omega)
        rw [← hevB] at hmodB
        wp_apply (hSend γ key γw r' fcs st.ch 1 (1 : Qp).half evsw M _ eps B.evs (DFrac.own 1))
          $$ [Hchf Hlv Ha Hsl] as %b ⟨Hchf, Hlv, Hsl, Ha⟩
        · rw [if_neg hBne]
          iframe Hmeta Hfx Hfo Hch Hchf Hlv Ha Hwf' Hsl HevB
          ipureintro
          refine ⟨Heplen, rfl, fun _ => rfl, fun ev hev => ?_, fun _ ev hev => ?_⟩
          · have := hmodB ev hev; rw [hcur]; omega
          · have := hmodB ev hev
            have : (sint.nat st.minRev : Int) = sint.Z st.minRev := by
              show ((sint.Z st.minRev).toNat : Int) = _; omega
            omega
        rw [if_neg hBne]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          wp_auto
          wp_apply wp_mapInsert $$ Hvm as Hvm
          (try wp_auto)
          wp_apply (mvcc.sw_wp_unsynced_delete hDel self s ws v.Wu W' m' key r' fcs hm')
            $$ [$Hun $Hm $Hfx] as %b ⟨Hun, Hm⟩
          (try wp_auto)
          generalize hst' : ({ st with minRev := B.moreRev, victim := true } :
            mvcc.WatcherSt) = st'
          have hst'm : sint.Z st'.minRev = M := by rw [← hst']; simp only; rw [hmrM]; exact hMz
          have hPBv0 : PBv !! key = none := by
            have := fbv; rw [Hl.bv, GMap.lookup_fmap] at this
            cases h : PBv !! key with
            | none => rfl
            | some _ => rw [h] at this; cases this
          ihave Hmw := mvcc.sw_memberRes_new_victim γ σ v key r' B st' γw fcs evsw M
            hM Hsr hvWs fvo ⟨by rw [hst'm]; omega, by
              show M = (sint.Z st'.minRev).toNat; rw [hst'm]; simp,
              fun _ => by rw [← hst'], fun ev hev => by
                have := hmodB ev hev
                have : (sint.nat st.minRev : Int) = sint.Z st.minRev := by
                  show ((sint.Z st.minRev).toNat : Int) = _; omega
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
          iframe Hst Hmem Hsynced Hun Hvm Hrem Hwbm w s curRev compactionRev victims wb
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
          refine ⟨Hl.step Hkey r' (.victim B) st' (evsw, M) _ _ hok'
            (by show <[key := B]> v.Bv = _; rw [Hl.bv, GMap.fmap_insert])
            (fun k hk => by
              show (GMap.delete key PBr) !! k = _
              exact GMap.lookup_delete_ne _ (Ne.symm hk)), ?_⟩
          cases self <;> rfl
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
          iframe Hst Hmem Hsynced Hun Hvm Hbv Hrem Hwbm w s curRev compactionRev victims wb
          ipureintro
          refine ⟨Hl.step Hkey r' .unsynced st' (evsw ++ B.evs, M) PBv _ hok' Hl.bv
            (fun k hk => by
              show (GMap.delete key PBr) !! k = _
              exact GMap.lookup_delete_ne _ (Ne.symm hk)), ?_⟩
          exact hm'

  isplitr
  · imodintro
    iintro %i %key %m' ⟨%Hkey, %Hu⟩ HP
    iNamed HP
    exfalso
    obtain ⟨Hl, hm'⟩ := Hi
    have hnot := mvcc.sw_not_mem_take keys Hknodup i key Hkey
    have hW : (W' !! key).isSome := by
      have := (Hkset key).1 (List.mem_of_getElem? Hkey)
      rw [GMap.domSet, GMap.lookup_fmap] at this; simpa using this
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hW
    obtain ⟨-, hu, -⟩ := Hl.rest key hnot
    subst hm'
    cases hs : self
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, GMap.domSet, GMap.lookup_fmap, hr] at Hu
      cases Hu
    · simp only [hs, ↓reduceIte, GMap.domSet, GMap.lookup_fmap, hu, hW'Wu key r hr] at Hu
      cases Hu
  iintro %m' HP Hm
  iNamed HP
  obtain ⟨Hl, hm'⟩ := Hi
  ihave Hunsynced : mvcc.ownWatcherGroup (mvcc.unsyncedAddr s) v.Wu $$ [Hun Hm]
  · cases hs : self
    · simp only [hs, Bool.false_eq_true, ↓reduceIte]; iexact Hun
    · simp only [hs, ↓reduceIte] at hm' ⊢
      subst hm'
      iapply (mvcc.ownWatcherGroup_at _ _ 1).2
      iexists ws
      iapply Hun
      iunfold mvcc.ownWatcherSet; iexact Hm
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
  generalize hvbs' : (if v.Bv.size = 0 then σ.vbs else σ.vbs ++ [vm]) = vbs'
  generalize hVB' : (if v.Bv.size = 0 then σ.VB else σ.VB ++ [v.Bv]) = VB'
  have hlen' : vbs'.length = VB'.length := by
    rw [← hvbs', ← hVB']; split <;> simp [Hvlen]
  wp_auto
  ihave %Hvsl := ownSlice_len _ _ _ $$ Hvs
  ihave IH : iprop(∃ (n vz : w64) (vv : GoMap),
      "i" ∷ i_ptr ↦ n ∗ "vsz" ∷ vsz_ptr ↦ vz ∗ "v" ∷ v_ptr ↦ vv ∗ "Hvs" ∷ vs' ↦* vbs' ∗
      "Hvbs" ∷ ([∗list] x ∈ vbs'.zip VB', mvcc.ownWatcherBatch x.1 x.2) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z vs'.len⌝) $$ [i vsz v Hvs Hvbs]
  · iexists W64 0, W64 0, _
    simp only [named]
    iframe
    ipureintro; exact ⟨by decide, Hvsl.2⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < vbs'.length := by rw [Hvsl.1]; word
    obtain ⟨vmap, Hvn⟩ : ∃ vmap, vbs'[sint.nat n]? = some vmap := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z vs'.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index vs' (sint.Z n) vbs' (DFrac.own 1) vmap Hn.1 $$ [Hvs] as Hvs
    · iframe; ipureintro; exact Hvn
    (try wp_auto)
    obtain ⟨Bn, HBn⟩ : ∃ Bn, VB'[sint.nat n]? = some Bn :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hlen']; exact Hlt)⟩
    have hz : (vbs'.zip VB')[sint.nat n]? = some (vmap, Bn) := by
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
    iexists n + W64 1, _, _
    simp only [named]
    iframe
    isplitl [Hvbs]
    · rw [mvcc.set_same hz]; iexact Hvbs
    ipureintro; constructor <;> word
  wp_apply (hSize (mvcc.unsyncedAddr s) v.Wu 1) $$ [$Hunsynced] as ⟨Hunsynced, -⟩
  (try wp_auto)
  iunfold gaugeSetSpec at HgSet
  rw [HgEq]
  wp_apply HgSet
  (try wp_auto)
  wp_apply (hSize (mvcc.unsyncedAddr s) v.Wu 1) $$ [$Hunsynced] as ⟨Hunsynced, -⟩
  (try wp_auto)
  -- the deferred `s.store.revMu.RUnlock()`
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HrevQ HclogQ HbucketQ HtoksQ HlogQ] as HrevMuR
  · inext
    iunfold mvcc.revMuInv
    iexists C, ntok
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨HneQ, HbudgetQ⟩
  (try wp_auto)
  -- the lock's final state
  subst hvbs' hVB'
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
  ihave HPf : mvcc.watchStoreBody s γ 1 σf $$ [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo
      Hmeta Hwt Hmem]
  · iunfold mvcc.watchStoreBody
    simp only [named]
    iframe Hσ Hwlog Hcert Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmfix
    isplitr
    · ipureintro; exact hlen'
    isplitl [Hmem]
    · iapply (BigSepM.bigSepM_mono (fun {k x} _ => ?_)) $$ Hmem
      rw [mvcc.sw_memberRes_congr γ 1 (v.st σ) σf k x rfl rfl rfl rfl (hvo k).symm]
    isplitr
    · iapply (BigSepM.bigSepM_mono (fun {k x} _ => by unfold mvcc.outRes; exact .rfl)) $$ Hout
    ipureintro; exact hokf
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl HPf]
  · inext; iunfold mvcc.watchStoreInv; iexists σf; iexact HPf
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
