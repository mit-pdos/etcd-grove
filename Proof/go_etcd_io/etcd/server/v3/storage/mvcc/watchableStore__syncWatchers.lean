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
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.SyncCompactLemmas

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
set_option maxHeartbeats 1000000 in
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
    ⟨%gP, #HgP, #HgPS⟩, -, #HmaxW, -, ⟨%gS', #HgS', #HgSet⟩, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold mvcc.watchReader at HR
  icases HR with ⟨Hsr0, Hmur⟩
  iunfold mvcc.storeReader at Hsr0; iunfold mvcc.storeReaderC at Hsr0
  iNamedSuffix Hsr0 "R"
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.watchStoreInv s γ 1)) $$ Hlc1 HP with HP
  iunfold mvcc.watchStoreInv at HP
  icases HP with ⟨%σ, HP, Hrel, Hwsf, %HsetR⟩
  obtain ⟨Hset, Hsrb, Hurst⟩ := HsetR
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
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl HP Hrel Hwsf]
    · inext; iunfold mvcc.watchStoreInv; iexists σ; iframe HP Hrel Hwsf; ipureintro; exact ⟨Hset, Hsrb, Hurst⟩
    (try wp_auto)
    iapply HΦ
    iunfold mvcc.watchReader
    iframe Hmur
    iunfold mvcc.storeReader; iunfold mvcc.storeReaderC
    simp only [named]
    iframe
  -- (M2, the storage side) an unsynced watcher: the store is frozen (`wsWatchFrozen`; until then
  -- `isWatchableStore`'s `crevFrozen`, now by the mode)
  have hszne : GMap.size σ.Wu ≠ 0 := fun h => Hif (by rw [h]; rfl)
  iclear Hfrz
  ihave #Hfrz := mvcc.wsWatchFrozen_of_Wu γ σ Hok hszne $$ Hwfz
  ihave #Hs0 : mvcc.isStore st γ.st $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamedSuffix Hs "S"
  -- the inner store's fields: the watchable store's share (D22 receiver epochs, S3)
  iunfold mvcc.wsFields at Hwsf
  icases Hwsf with ⟨%st', #Hst', Hwsf, Hwsd⟩
  ihave #Hstp : s.[watchableStore, go!"store"] ↦□ st $$ []
  · iunfold mvcc.isWatchableStore at HwsAll; iNamed HwsAll; iexact Hst
  icombine Hstp Hst' gives %Hsteq
  subst Hsteq
  -- the share at the current physical names `p` (D22 receiver epochs, S5b): the backend's reads
  -- are at `γ.st.withPhys p`
  iunfold mvcc.fieldShare at Hwsf
  icases Hwsf with ⟨%p, %o, Hwsf⟩
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HrevMuR] as ⟨Hrl, HQ⟩
  wp_auto_lc 2
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv st γ.st sync.rfrac)) $$ Hlc1 HQ with HQ
  icases mvcc.revMuInv_open_share st γ.st p _ _ o $$ [HQ Hwsf] with ⟨HQ, HrstR, Hwsf⟩
  · iframe HQ Hwsf
  -- a slot of the readers' pool, for the snapshot's backend token: checked out under the watchable
  -- store's lock, with its deposit (D22 receiver epochs, S5a), at the share's pin (S5b)
  iunfold mvcc.fieldShareAt at Hwsf
  iNamed Hwsf
  imod mvcc.readerPool_checkout_ws_p γ.st p _ o $$ Hlc2 HpoolS Hcur HtkR [Hwsd] with ⟨Hslot, Htkw, Hcur⟩
  · iunfold mvcc.wsDep; iexact Hwsd
  iunfold mvcc.idxSlot at Hslot
  icases Hslot with ⟨HtiP, HrtR⟩
  ihave #HphS := Hph
  iunfold mvcc.physOk at HphS
  iNamedSuffix HphS "S"
  iunfold mvcc.storeFields at Hflds
  iNamed Hflds
  iunfold mvcc.revMuBody at HQ
  icases HQ with ⟨%C, %ntok, %cQ, HQ⟩
  iNamedSuffix HQ "Q"
  -- (watches across a compaction) the compaction revision `cQ`: `-1` (no compactor) or a revision
  -- of the committed log that writes no key twice (the create token's `watchNoDup`); a member
  -- `choose` marks compacted is behind it (`crevLb`)
  imod mvcc.watchNoDup_crev γ.st _ cQ C HcQ.1 $$ Hfrz HcrevQ HcertQ HokQ with ⟨HcrevQ, %HndQ⟩
  icases mvcc.crevUB_get_lb _ _ _ $$ HcrevQ with ⟨HcrevQ, #HlbQ⟩
  icases persistent_entails_right (mvcc.idxLogAuth_cert_prefix _ _ _ _) $$ [$HlogQ $Hcert]
    with ⟨%HpC, HlogQ, -⟩
  -- under `s.mu`, the committed log is the notified one (unit W-K)
  icases persistent_entails_right (mvcc.wlogQ_auth_agree (GF := GF) γ _ _ σ.Lmu C) $$
    [$Hwlog $HlogQ] with ⟨%HCL, Hwlog, HlogQ⟩
  -- (D25) the committed log is released
  ihave #HrlC0 := monoNatLbOwn_get γ.rel 1 _ $$ Hrel
  ihave #HrlC : mvcc.relLb γ C.length $$ []
  · iunfold mvcc.relLb; rw [HCL]; iexact HrlC0
  wp_auto
  -- the unsynced members' states, for `choose`
  icases persistent_entails_right (mvcc.sw_unsynced_bounds γ σ Hok _ C) $$ [$Hmem $HlogQ]
    with ⟨%Hbd, Hmem, HlogQ⟩
  icases persistent_entails_right (mvcc.sw_unsynced_cmp γ σ Hok _ cQ HcQ.1) $$ [$Hmem $HcrevQ]
    with ⟨%Hcmp0, Hmem, HcrevQ⟩
  have hCne : 1 ≤ C.length := List.length_pos_iff.2 HneQ
  have hClt : C.length < 2 ^ 63 := by
    have := HbudgetQ; omega
  icases (mvcc.sw_bigSepM_split (fun k _ => (σ.Wu !! k).isSome) σ.ST _).1 $$ Hst with ⟨Hstu, Hstr⟩
  icases (mvcc.sw_bigSepM_split (fun k _ => (σ.Wu !! k).isSome) σ.ST _).1 $$ Hmem with ⟨Hmemu, Hmemr⟩
  have hSTu : ∀ k, (Iris.Std.PartialMap.filter (fun k _ => (σ.Wu !! k).isSome) σ.ST : GMap Loc mvcc.WatcherSt) !! k =
      if (σ.Wu !! k).isSome then σ.ST !! k else none := by
    intro k; rw [mvcc.sw_filter_lookup]; cases σ.ST !! k <;> cases (σ.Wu !! k).isSome <;> rfl
  generalize hSTuD : (Iris.Std.PartialMap.filter (fun k _ => (σ.Wu !! k).isSome) σ.ST : GMap Loc mvcc.WatcherSt) = STu at hSTu ⊢
  have hcur : sint.Z (W64 ((C.length : Int) - 1)) = (C.length : Int) - 1 := by word
  have hcQ : sint.Z (W64 cQ : w64) = cQ := by have := HbudgetQ; word
  -- (watches across a compaction) the members' parts of `choose`'s compaction sends
  ihave Hmemu := BigSepM.bigSepM_mono (Φ := fun k x => mvcc.memberRes (GF := GF) γ 1 σ k x)
      (Ψ := fun k x => iprop((if decide (sint.Z x.minRev < sint.Z (W64 cQ : w64)) then
          mvcc.cmpSendPre γ k x.ch (1 : Qp).half else iprop(True)) ∗
        ((if decide (sint.Z x.minRev < sint.Z (W64 cQ : w64)) then
          mvcc.cmpSendPre γ k x.ch (1 : Qp).half else iprop(True)) -∗ mvcc.memberRes γ 1 σ k x)))
      (fun {k x} hk => by
        have hk' : STu !! k = some x := hk
        rw [hSTu] at hk'
        split at hk'
        · rename_i hu
          exact mvcc.memberRes_cmp_split γ σ k x (W64 cQ) (Or.inr (Or.inl hu))
        · cases hk') $$ Hmemu
  irevert Hmemu
  rw [BigSepM.bigSepM_sep_eq]
  iintro ⟨Hpre, Hwands⟩
  wp_apply (hChoose γ (1 : Qp).half (mvcc.unsyncedAddr s) σ.Wu STu (W64 512) (W64 ((C.length : Int) - 1))
      (W64 cQ))
    $$ [$Hunsynced Hstu Hpre] as %g %minRev Hch
  · iunfold mvcc.ownStates; iframe Hstu Hpre
    ipureintro
    refine ⟨⟨fun w hw => ?_, fun w st hw => ?_⟩, by have := Hok.wu_size; omega⟩
    · rw [hSTu, if_pos hw]; exact Hok.live_st w (Or.inr (Or.inl hw))
    · rw [hSTu] at hw
      split at hw
      · rename_i hu
        have := (Hbd w st hw hu).1
        -- at or below `curRev`, or restoring (D22 receiver epochs, S6: `WsState.unsRst`)
        refine ⟨this, ?_⟩
        rcases Hurst w st hu hw with h | h
        · left; rw [hcur]; rw [← HCL] at h; omega
        · right; exact h
      · cases hw
  icases Hch with ⟨%W0, %Cm, %HWC, Hbr, Hstu, Hpre, %hminR⟩
  obtain ⟨hW0sub, hCm⟩ := HWC
  -- (watches across a compaction) the members sent the compaction response (`Cm`) left the chosen
  -- group (`W'`), and in the group branch the unsynced one
  ihave Hbr : ∃ (self : Bool), ⌜self = true → g = mvcc.unsyncedAddr s ∧ W0 = σ.Wu⌝ ∗
      mvcc.ownWatcherGroup g (Iris.Std.PartialMap.filter (fun w _ => !(Cm !! w).isSome) W0) ∗
      (if self then iprop(True) else mvcc.ownWatcherGroup (mvcc.unsyncedAddr s) σ.Wu) $$ [Hbr]
  · icases Hbr with (⟨%H1, Hg⟩ | ⟨-, Hun, Hg⟩)
    · iexists true
      obtain ⟨rfl, rfl, -⟩ := H1
      iframe Hg
      isplitr
      · ipureintro; exact fun _ => ⟨rfl, rfl⟩
      simp only [↓reduceIte]; itrivial
    · iexists false
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hg Hun
      ipureintro; exact fun h => by cases h
  icases Hbr with ⟨%self, %hself0, Hg, Hun⟩
  generalize hW'D : (Iris.Std.PartialMap.filter (fun w _ => !(Cm !! w).isSome) W0 :
    GMap Loc mvcc.WatchRange) = W'
  have hW'0 : ∀ w r, W' !! w = some r → W0 !! w = some r ∧ (Cm !! w).isSome = false := by
    intro w r h
    rw [← hW'D, mvcc.sw_filter_lookup] at h
    cases h0 : W0 !! w with
    | none => rw [h0] at h; cases h
    | some r0 =>
      rw [h0] at h
      cases hc : (Cm !! w).isSome
      · simp only [hc, Bool.not_false, ↓reduceIte, Option.bind_some, Option.some.injEq] at h
        exact ⟨by rw [h], rfl⟩
      · simp [hc] at h
  have hCmWu : ∀ w, (Cm !! w).isSome → (σ.Wu !! w).isSome := by
    intro w hw
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (hCm w hw).1
    rw [hW0sub w r hr]; rfl
  have hW0dom : ∀ k, (domSet W0 !! k).isSome → (σ.Wu !! k).isSome := by
    intro k hk
    have hk' : (W0 !! k).isSome := by rw [GMap.domSet, GMap.lookup_fmap] at hk; simpa using hk
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hk'
    rw [hW0sub k r hr]; rfl
  generalize hWu1D : (if self then W' else σ.Wu) = Wu1
  have hWu1 : ∀ w, Wu1 !! w = σ.Wu !! w ∨ ((Cm !! w).isSome ∧ Wu1 !! w = none) := by
    intro w
    rw [← hWu1D]
    cases hs : self
    · left; rfl
    · obtain ⟨-, hW0⟩ := hself0 hs
      simp only [↓reduceIte]
      rw [← hW'D, mvcc.sw_filter_lookup, hW0]
      cases hc : (Cm !! w).isSome
      · left; cases σ.Wu !! w <;> simp [hc]
      · right; refine ⟨rfl, ?_⟩; cases σ.Wu !! w <;> simp [hc]
  have hself : self = true → g = mvcc.unsyncedAddr s ∧ W' = Wu1 := by
    intro hs; refine ⟨(hself0 hs).1, ?_⟩; rw [← hWu1D, hs]; rfl
  have hW'Wu : ∀ w r, W' !! w = some r → σ.Wu !! w = some r :=
    fun w r h => hW0sub w r (hW'0 w r h).1
  have hW'Wu1 : ∀ w r, W' !! w = some r → Wu1 !! w = some r := by
    intro w r h
    rcases hWu1 w with e | ⟨hc, -⟩
    · rw [e]; exact hW'Wu w r h
    · rw [(hW'0 w r h).2] at hc; cases hc
  -- (D22 receiver epochs, S6; watches across a compaction) the states after `choose` (restore
  -- reset, compaction responses): the chosen members' (`STu'`) and all (`ST0`), the loop's initial
  -- ones
  generalize hSTu'D : mvcc.chooseCmp Cm (mvcc.chooseRst (W64 ((C.length : Int) - 1)) (domSet W0) STu)
    = STu'
  have hSTu' : ∀ k, STu' !! k =
      (STu !! k).map (mvcc.chooseF (W64 ((C.length : Int) - 1)) (domSet W0) Cm k) := by
    intro k; rw [← hSTu'D, mvcc.chooseCmp_chooseRst_lookup]
  generalize hST0D : mvcc.chooseCmp Cm (mvcc.chooseRst (W64 ((C.length : Int) - 1)) (domSet W0) σ.ST)
    = ST0
  have hST0 : ∀ k, ST0 !! k =
      (σ.ST !! k).map (mvcc.chooseF (W64 ((C.length : Int) - 1)) (domSet W0) Cm k) := by
    intro k; rw [← hST0D, mvcc.chooseCmp_chooseRst_lookup]
  have hW'ST : ∀ w, (W' !! w).isSome → ∃ st, STu' !! w = some st ∧ ST0 !! w = some st := by
    intro w hw
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hw
    have hu : (σ.Wu !! w).isSome := by rw [hW'Wu w r hr]; rfl
    obtain ⟨st, hst⟩ := Option.isSome_iff_exists.1 (Hok.live_st w (Or.inr (Or.inl hu)))
    exact ⟨_, by rw [hSTu', hSTu, if_pos hu, hst]; rfl, by rw [hST0, hst]; rfl⟩
  have Hbd0 : ∀ w st, ST0 !! w = some st → (σ.Wu !! w).isSome →
      0 ≤ sint.Z st.minRev ∧ ∀ γw, σ.M !! w = some γw → sint.nat st.minRev ≤ max γw.lo C.length := by
    intro w st hs hu
    rw [hST0] at hs
    cases h0 : σ.ST !! w with
    | none => rw [h0] at hs; cases hs
    | some st0 =>
      rw [h0] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      have e : st.minRev = st0.minRev := by rw [← hs]; simp
      rw [e]; exact Hbd w st0 h0 hu
  -- (watches across a compaction) the range's lower bound: the least `minRev` of the chosen
  -- members not behind the compaction revision, so at least it
  obtain ⟨hm0, hm2⟩ := mvcc.sw_minRevOf_lb STu
    (Iris.Std.PartialMap.filter (fun w _ => mvcc.notBehind STu (W64 cQ) w) (domSet W0))
    (fun w st _ hs => by
      rw [hSTu] at hs
      split at hs
      · rename_i hu; exact (Hbd w st hs hu).1
      · cases hs)
  have hmQ : cQ ≤ mvcc.minRevOf STu
      (Iris.Std.PartialMap.filter (fun w _ => mvcc.notBehind STu (W64 cQ) w) (domSet W0)) := by
    refine mvcc.minRevOf_ge _ _ cQ (by have := HcQ.2; omega) (fun w st hw hs => ?_)
    rw [mvcc.sw_filter_lookup] at hw
    cases h0 : domSet W0 !! w with
    | none => rw [h0] at hw; cases hw
    | some u =>
      rw [h0] at hw
      unfold mvcc.notBehind at hw; rw [hs] at hw
      by_cases hc : sint.Z (W64 cQ : w64) ≤ sint.Z st.minRev
      · rw [hcQ] at hc; exact hc
      · exfalso
        simp only [decide_eq_false hc] at hw
        simp at hw
  rw [← hminR] at hm0 hm2 hmQ
  have hm2' : ∀ w st, (W' !! w).isSome → STu' !! w = some st → cQ ≤ sint.Z st.minRev →
      sint.Z minRev ≤ sint.Z st.minRev := by
    intro w st hw hs hq
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hw
    rw [hSTu'] at hs
    cases h0 : STu !! w with
    | none => rw [h0] at hs; cases hs
    | some st0 =>
      rw [h0] at hs; simp only [Option.map_some, Option.some.injEq] at hs
      have e : st.minRev = st0.minRev := by rw [← hs]; simp
      rw [e] at hq ⊢
      refine hm2 w st0 ?_ h0
      rw [mvcc.sw_filter_lookup, GMap.domSet, GMap.lookup_fmap, (hW'0 w r hr).1]
      unfold mvcc.notBehind; rw [h0]; simp [hcQ, hq]
  ihave %HCwf : ⌜mvcc.LogWf' C ∧ C.length < 2 ^ 63 ∧ ∀ cs ∈ C, cs.length < 2 ^ 63⌝ $$ [HcertQ]
  · iunfold mvcc.idxCert at HcertQ
    icases HcertQ with ⟨-, %H, -⟩
    ipureintro; exact H
  have hcur1 : sint.Z (W64 ((C.length : Int) - 1) + W64 1) = (C.length : Int) := by word
  ihave #HcertP : mvcc.idxCert (γ.st.withPhys p).idx C $$ []
  · rw [mvcc.idxCert_withPhys]; iexact HcertQ
  ihave #HbkS := mvcc.isKeyBackendG_wand $$ HbkS
  wp_apply (lc := 1) (hRange _ _ (γ.st.withPhys p) _ _ _ _ C minRev (W64 ((C.length : Int) - 1) + W64 1) g W')
    $$ [$HbkS $HrtR HcrevQ $HbucketQ $HcertP $Hg] as %evs ⟨HrtR, HcrevQ, HbucketQ, Hg, %ps, Hevs,
      Hevcap, %Hpslen, #HevIs⟩
  · rw [mvcc.crevUB_withPhys]; iframe HcrevQ
    ipureintro; rw [hcur1]
    exact ⟨hm0, by omega, by omega, HcQ.1, hmQ, HndQ⟩
  -- the slot back in the readers' pool, the watchable store's deposit back (S5a)
  imod mvcc.readerPool_checkin_ws_p γ.st p _ o $$ Hlc1 HpoolS Hcur [HtiP HrtR] Htkw with ⟨HtkR, Hwsd, Hcur⟩
  · iunfold mvcc.idxSlot; iframe HtiP HrtR
  iunfold mvcc.wsDep at Hwsd
  have hnat1 : sint.nat (W64 ((C.length : Int) - 1) + W64 1) = C.length := by
    show (sint.Z _).toNat = _; rw [hcur1]; simp
  rw [hnat1] at Hpslen ⊢
  generalize hevm : (mvcc.logEvents C (sint.nat minRev) C.length).filter
    (fun ev => mvcc.wgCovers W' ev.kv.key) = evm at Hpslen ⊢
  (try wp_auto)
  rw [go.make1_underlying, go.is_underlying (t := watcherBatch.ty)]
  wp_apply (wp_map_make1 (K := Loc) (V := Loc)) as %vm Hvm
  (try wp_auto)
  wp_apply (hNWB g W' STu' evs (DFrac.own 1) ps evm) $$ [$Hg Hstu $Hevs $HevIs]
    as %wb ⟨Hg, Hstu, Hevs, Hwb⟩
  · iframe Hstu
    ipureintro
    refine ⟨fun w hw => ?_, Hpslen⟩
    obtain ⟨st, h1, -⟩ := hW'ST w hw; rw [h1]; rfl
  iunfold mvcc.ownStates at Hstu
  have hsplit1 : (Iris.Std.PartialMap.filter (fun k _ => (σ.Wu !! k).isSome) ST0 :
      GMap Loc mvcc.WatcherSt) = STu' := by
    refine GMap.ext (fun k => ?_)
    show (Iris.Std.PartialMap.filter (fun k _ => (σ.Wu !! k).isSome) ST0 : GMap Loc mvcc.WatcherSt) !! k
      = STu' !! k
    rw [mvcc.sw_filter_lookup, hST0, hSTu', hSTu]
    cases (σ.Wu !! k).isSome <;> cases σ.ST !! k <;> rfl
  have hsplit2 : (Iris.Std.PartialMap.filter (fun k x => !(fun k _ => (σ.Wu !! k).isSome) k x) ST0 :
      GMap Loc mvcc.WatcherSt) =
      Iris.Std.PartialMap.filter (fun k x => !(fun k _ => (σ.Wu !! k).isSome) k x) σ.ST := by
    refine GMap.ext (fun k => ?_)
    show (Iris.Std.PartialMap.filter _ ST0 : GMap Loc mvcc.WatcherSt) !! k =
      (Iris.Std.PartialMap.filter _ σ.ST : GMap Loc mvcc.WatcherSt) !! k
    rw [mvcc.sw_filter_lookup, mvcc.sw_filter_lookup, hST0]
    cases hu : (σ.Wu !! k).isSome
    · have hd : (domSet W0 !! k).isSome = false := by
        cases h : (domSet W0 !! k).isSome
        · rfl
        · have := hW0dom k h; rw [hu] at this; cases this
      have hc : (Cm !! k).isSome = false := by
        cases h : (Cm !! k).isSome
        · rfl
        · have := hCmWu k h; rw [hu] at this; cases this
      cases σ.ST !! k with
      | none => rfl
      | some st0 =>
        simp only [Option.map_some, mvcc.chooseF_of _ _ _ _ _ hd hc, Option.bind_some, hu]
    · cases σ.ST !! k <;> simp [hu]
  ihave Hst := (mvcc.sw_bigSepM_split (fun k _ => (σ.Wu !! k).isSome) ST0 _).2 $$ [Hstu Hstr]
  · rw [hsplit1, hsplit2]; iframe
  -- (watches across a compaction) the members' resources back from `choose`'s sends, in the state
  -- after it: the ones marked compacted behind the compaction revision
  icombine Hpre Hwands as Hpw
  irevert Hpw
  rw [BigSepM.bigSepM_sep_eq_symm]
  iintro Hpw
  ihave Hmemu : [∗map] k ↦ x ∈ STu, mvcc.memberRes (GF := GF) γ 1 σ k x $$ [Hpw]
  · iapply (BigSepM.bigSepM_mono (fun {k x} _ => by iintro ⟨H1, H2⟩; iapply H2 $$ H1)) $$ Hpw
  ihave Hmem := (mvcc.sw_bigSepM_split (fun k _ => (σ.Wu !! k).isSome) σ.ST _).2 $$ [Hmemu Hmemr]
  · rw [hSTuD]; iframe
  -- the lock's facts in the state after `choose`
  have hcm := (mvcc.WsOk.cmpSt (Hok.chooseRst_ST (W64 ((C.length : Int) - 1)) (domSet W0)) Cm Wu1
    hCmWu hWu1)
  have hX1 : ({ σ with Wu := Wu1, ST := ST0 } : mvcc.WsState) =
      ({ σ with ST := mvcc.chooseRst (W64 ((C.length : Int) - 1)) (domSet W0) σ.ST } :
        mvcc.WsState).cmpSt Cm Wu1 := by rw [← hST0D]; rfl
  have hok1 : mvcc.WsOk { σ with Wu := Wu1, ST := ST0 } := by rw [hX1]; exact hcm.1
  have hlive1 : ∀ k, ({ σ with Wu := Wu1, ST := ST0 } : mvcc.WsState).live k ↔ σ.live k := by
    intro k; rw [hX1]; exact (hcm.2 k).trans (mvcc.chooseRst_live σ _ _ k)
  have hset1 : ({ σ with Wu := Wu1, ST := ST0 } : mvcc.WsState).settled := by
    rw [hX1]; exact mvcc.WsState.settled_cmpSt (mvcc.WsState.settled_chooseRst Hset _ _) Cm Wu1

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
  ihave Hun : (if self then (mvcc.ownWatcherSet ws (domSet Wu1) -∗
      mvcc.ownWatcherGroupAt (mvcc.unsyncedAddr s) Wu1 ws)
      else mvcc.ownWatcherGroup (mvcc.unsyncedAddr s) Wu1) $$ [Hun Hrest]
  · cases hs : self
    · have e : Wu1 = σ.Wu := by rw [← hWu1D, hs]; rfl
      rw [e]; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hun
    · obtain ⟨rfl, hW⟩ := hself hs
      rw [← hW]
      simp only [↓reduceIte]
      iexact Hrest
  iunfold mvcc.ownWatcherSet at Hws
  -- (watches across a compaction) every chosen member sent the compaction response: no batch map
  ihave Hwb : ∃ PB : GMap Loc (Loc × mvcc.EventBatch),
      (⌜W' = ∅⌝ ∨ wb ↦$ GMap.fmap Prod.fst PB) ∗
      ⌜W' = ∅ ∨ mvcc.batchOf W' STu' evm = GMap.fmap Prod.snd PB⌝ ∗
      ([∗map] _w ↦ p ∈ PB, ⌜p.1 ≠ null⌝ ∗ mvcc.ownEventBatch p.1 p.2) $$ [Hwb]
  · icases Hwb with (%hW0 | ⟨-, Hwb⟩)
    · iexists ∅
      isplitr
      · ileft; ipureintro; exact hW0.1
      isplitr
      · ipureintro; exact Or.inl hW0.1
      iapply BigSepM.bigSepM_empty.2; iempintro
    · iunfold mvcc.ownWatcherBatch at Hwb
      icases Hwb with ⟨%PB, Hwbm, %HBt, Hbs⟩
      iexists PB
      iframe Hbs
      isplitl [Hwbm]
      · iright; iexact Hwbm
      ipureintro; exact Or.inr HBt
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
      "Hwbm" ∷ (⌜W' = ∅⌝ ∨ wb ↦$ GMap.fmap Prod.fst PB) ∗
      "w" ∷ w_ptr ↦ wv ∗ "s" ∷ s_ptr ↦ s ∗
      "curRev" ∷ curRev_ptr ↦ W64 ((C.length : Int) - 1) ∗
      "compactionRev" ∷ compactionRev_ptr ↦ W64 cQ ∗
      "victims" ∷ victims_ptr ↦ vm ∗ "wb" ∷ wb_ptr ↦ wb ∗
      "%Hi" ∷ ⌜mvcc.SyncLoop { σ with Wu := Wu1 } ST0 v PB PBv PBr keys i ∧
        m' = (if self then domSet v.Wu else domSet W')⌝))
    _ _ _ ws (domSet W') (DFrac.own 1)) $$ Hws
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hst Hmem Hsynced Hun Hvm Hbs Hwbm w s curRev compactionRev victims wb]
  · -- (D22 receiver epochs, S6; watches across a compaction) the loop starts from the state after
    -- `choose`: its reset and compacted states `ST0`, the unsynced group `Wu1`
    iexists mvcc.SyncVars.init { σ with Wu := Wu1, ST := ST0 }, ∅, PB, zero_val Loc
    simp only [named, GMap.fmap_empty]
    have hI : ∀ k, (mvcc.SyncVars.st σ (mvcc.SyncVars.init { σ with Wu := Wu1, ST := ST0 })).victimOf k =
        σ.victimOf k := by
      intro k; rw [mvcc.SyncVars.st_victimOf]; simp [mvcc.SyncVars.init]
    iframe Hvm Hwbm w s curRev compactionRev victims wb Hbs
    have e1 : (mvcc.SyncVars.init { σ with Wu := Wu1, ST := ST0 }).ST = ST0 := rfl
    have e2 : (mvcc.SyncVars.init { σ with Wu := Wu1, ST := ST0 }).Ws = σ.Ws := rfl
    have e3 : (mvcc.SyncVars.init { σ with Wu := Wu1, ST := ST0 }).Wu = Wu1 := rfl
    rw [e1, e2, e3]
    iframe Hst Hsynced Hun
    isplitl [Hmem]
    · iapply (BigSepM.bigSepM_mono (Φ := fun k x => mvcc.memberRes (GF := GF) γ 1 { σ with Wu := Wu1, ST := ST0 } k x)
        (fun {k x} _ => by
          rw [mvcc.sw_memberRes_congr γ 1 (mvcc.SyncVars.st σ (mvcc.SyncVars.init { σ with Wu := Wu1, ST := ST0 }))
            { σ with Wu := Wu1, ST := ST0 } k x rfl rfl rfl rfl (hI k) rfl]))
      iapply (show ([∗map] k ↦ x ∈ mvcc.gmapMapK (mvcc.chooseF (W64 ((C.length : Int) - 1)) (domSet W0) Cm)
          σ.ST, mvcc.memberRes (GF := GF) γ 1 { σ with Wu := Wu1, ST := ST0 } k x) ⊢
          [∗map] k ↦ x ∈ ST0, mvcc.memberRes γ 1 { σ with Wu := Wu1, ST := ST0 } k x
        from by rw [← mvcc.chooseCmp_chooseRst]; (try rw [hST0D]))
      iapply (mvcc.bigSepM_gmapMapK _ _ _).2
      iapply BigSepM.bigSepM_impl $$ Hmem
      imodintro
      iintro %k %x %hk H
      have hk' : σ.ST !! k = some x := hk
      cases hu : (σ.Wu !! k).isSome
      · -- not unsynced: untouched
        have hd : (domSet W0 !! k).isSome = false := by
          cases h : (domSet W0 !! k).isSome
          · rfl
          · have := hW0dom k h; rw [hu] at this; cases this
        have hc : (Cm !! k).isSome = false := by
          cases h : (Cm !! k).isSome
          · rfl
          · have := hCmWu k h; rw [hu] at this; cases this
        rw [mvcc.chooseF_of _ _ _ _ _ hd hc]
        have h1 : (Wu1 !! k).isSome = (σ.Wu !! k).isSome := by
          rcases hWu1 k with e | ⟨hc', -⟩
          · rw [e]
          · rw [hc] at hc'; cases hc'
        have h2 : ST0 !! k = σ.ST !! k := by
          simp only [hST0, hk', Option.map_some, mvcc.chooseF_of _ _ _ _ _ hd hc]
        iapply (mvcc.memberRes_congr γ 1 σ { σ with Wu := Wu1, ST := ST0 } k x rfl rfl h1 rfl rfl h2)
          $$ H
      · -- unsynced: marked compacted only behind the compaction revision
        have hws0 : σ.Ws !! k = none := by
          cases h : σ.Ws !! k with
          | none => rfl
          | some _ => have := Hok.ws_wu k (by rw [h]; rfl); rw [this] at hu; cases hu
        iapply (mvcc.memberRes_cmpSt γ σ { σ with Wu := Wu1, ST := ST0 } k x _ cQ rfl rfl rfl rfl hws0 hu (Hok.wu_v k hu)
          ((hlive1 k).2 (Or.inr (Or.inl hu))) (mvcc.chooseF_minRev _ _ _ _ _)
          (mvcc.chooseF_ch _ _ _ _ _) (fun hc => ?_))
        · rcases mvcc.chooseF_compacted _ _ _ _ _ hc with h | h
          · exact Or.inl h
          · obtain ⟨-, st1, hst1, hlt⟩ := hCm k h
            rw [hSTu, if_pos hu, hk'] at hst1; cases hst1
            right; rw [hcQ] at hlt; exact hlt
        isplitl [H]
        · iexact H
        iexact HlbQ
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    ipureintro
    refine ⟨⟨hok1.sync_init, by rw [GMap.fmap_empty]; rfl, fun k _ => by
      simp [mvcc.SyncVars.init],
      mvcc.WsState.settled_congr hset1 rfl rfl rfl rfl rfl rfl hI,
      fun k st hk => by simp at hk⟩, ?_⟩

    cases hs : self
    · rfl
    · obtain ⟨-, rfl⟩ := hself hs; rfl
  isplitr
  · imodintro
    iintro %i %key %u %m' ⟨%Hkey, %Hu⟩ HP Hm
    iNamed HP
    obtain ⟨Hl, hm'⟩ := Hi
    have hnot := not_mem_take_of_nodup Hknodup Hkey
    have hW : (W' !! key).isSome := by
      have := (Hkset key).1 (List.mem_of_getElem? Hkey)
      rw [GMap.domSet, GMap.lookup_fmap] at this; simpa using this
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hW
    obtain ⟨st, hSTuk, hσST⟩ := hW'ST key hW
    have hσWu : σ.Wu !! key = some r := hW'Wu key r hr
    obtain ⟨hvST, hvWu, hvWs, hvE, hvBv, hPBr⟩ := Hl.rest key hnot
    rw [hσST] at hvST
    have hvWu : v.Wu !! key = some r := hvWu.trans (hW'Wu1 key r hr)
    have hσWu : σ.Wu !! key = some r := hW'Wu key r hr
    have hσWs : σ.Ws !! key = none := by
      cases h : σ.Ws !! key with
      | none => rfl
      | some _ => have := Hok.ws_wu key (by rw [h]; rfl); rw [hσWu] at this; cases this
    rw [hσWs] at hvWs
    obtain ⟨hm0', hmC'⟩ := Hbd0 key st hσST (by rw [hσWu]; rfl)
    have hvST' : Iris.Std.PartialMap.get? v.ST key = some st := by rw [gmap_get?_eq]; exact hvST
    icases (BigSepM.bigSepM_delete hvST').1 $$ Hst with ⟨Hstw, Hst⟩
    iunfold mvcc.watcherOwn at Hstw
    icases Hstw with ⟨HminRev, Hvict, Hcomp, Hrest0, Hchf⟩
    wp_auto
    by_cases hskip : sint.Z st.minRev < cQ
    · -- (watches across a compaction) behind the compaction revision, its compaction response not
      -- sent (its channel full): skipped, `choose` retries it next time
      rw [decide_eq_true (show sint.Z st.minRev < sint.Z (W64 cQ : w64) by rw [hcQ]; exact hskip)]
      wp_auto
      ihave Hstw : mvcc.watcherOwn key st $$ [HminRev Hvict Hcomp Hrest0 Hchf]
      · iunfold mvcc.watcherOwn; iframe
      ihave Hst := (BigSepM.bigSepM_delete (Φ := fun w x => mvcc.watcherOwn (GF := GF) w x) hvST').2
        $$ [Hstw Hst]
      · isplitl [Hstw]
        · iexact Hstw
        iexact Hst
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hm
      iexists v, PBv, PBr, key
      simp only [named]
      iframe Hst Hmem Hsynced Hun Hvm Hbv Hrem Hwbm w s curRev compactionRev victims wb
      ipureintro
      refine ⟨Hl.skip Hkey (fun st0 _ hs => ?_), hm'⟩
      rw [hvST] at hs; cases hs
      show sint.Z st.minRev < (σ.Lmu.length : Int)
      rw [← HCL]; have := HcQ.2; omega
    rw [decide_eq_false (show ¬ sint.Z st.minRev < sint.Z (W64 cQ : w64) by rw [hcQ]; exact hskip)]
    wp_auto
    -- not compacted: a compacted unsynced member is behind the compaction revision
    have hcp0 : st.compacted = false := by
      have h2 := hσST
      cases h1 : σ.ST !! key with
      | none => rw [hST0, h1] at h2; cases h2
      | some st1 =>
        rw [hST0, h1] at h2
        simp only [Option.map_some, Option.some.injEq] at h2
        cases hc : st.compacted
        · rfl
        · exfalso
          rw [← h2] at hc
          rcases mvcc.chooseF_compacted _ _ _ _ _ hc with h | h
          · have := Hcmp0 key st1 h1 (by rw [hσWu]; rfl) h
            have e : st.minRev = st1.minRev := by rw [← h2]; simp
            rw [e] at hskip; omega
          · rw [(hW'0 key r hr).2] at h; cases h
    icases (BigSepM.bigSepM_delete hvST').1 $$ Hmem with ⟨Hmemw, Hmem⟩
    icases mvcc.sw_memberRes_unsynced γ 1 (v.st σ) key st hvWs (by show (v.Wu !! key).isSome; rw [hvWu]; rfl)
      $$ Hmemw with ⟨%γw, %r', %fcs, %evsw, %hM, #Hmeta, #Hfx, #Hch, #Hfo, %Hsr, %hE, Ha, Hlv, %Hlo,
        #Hwf, ⟨%Lc, #HLc, %HLc⟩, #Hcmpw⟩
    icases (BigSepM.bigSepM_lookup_acc (m := W') (by rw [gmap_get?_eq]; exact hr)).1 $$ Hfixed
      with ⟨⟨%fcs0, #Hf0⟩, -⟩
    ihave %Hag := mvcc.watcherFixed_agree key r' r fcs fcs0 $$ [$Hfx $Hf0]
    obtain ⟨rfl, -⟩ := Hag
    by_cases hmC : sint.Z st.minRev < C.length
    rotate_left
    · -- (D22 receiver epochs, S6) beyond the committed log: a watcher `watchableStore.Restore`
      -- moved (`chooseAll` cleared its restore flag); no event from its `minRev`: synced there
      wp_apply mvcc.sw_wp_max_int64
      rw [if_neg (show ¬ sint.Z st.minRev < sint.Z (W64 ((C.length : Int) - 1) + W64 1) by
        rw [hcur1]; omega)]
      (try wp_auto)
      icases Hwbm with (%hWe | Hwbm)
      · exfalso; rw [hWe] at hW; simp at hW
      wp_apply wp_map_lookup2 $$ Hwbm as Hwbm
      ihave Hwbm : (⌜W' = ∅⌝ ∨ wb ↦$ GMap.fmap Prod.fst PB) $$ [Hwbm]
      · iright; iexact Hwbm
      have HBt : mvcc.batchOf W' STu' evm = GMap.fmap Prod.snd PB :=
        HBt.resolve_left (fun hWe => by rw [hWe] at hW; simp at hW)
      have hbk : GMap.fmap Prod.snd PB !! key = mvcc.memberBatch r' st evm := by
        rw [← HBt, mvcc.batchOf_lookup, hr, hSTuk]
      have hmb := mvcc.memberBatch_logEvents C HCwf.1 HCwf.2.1 HCwf.2.2 r' st
        (fun ev => mvcc.wgCovers W' ev.kv.key) (sint.nat minRev) C.length
        (fun ev hc => by
          simp only [mvcc.wgCovers, decide_eq_true_eq]; exact ⟨key, r', hr, hc⟩)
        (by
          have := hm2' key st hW hSTuk (by omega)
          show ((sint.Z minRev).toNat : Int) ≤ _; omega)
        (Nat.le_refl _)
      rw [hevm] at hmb
      have hmCn : C.length ≤ sint.nat st.minRev := by
        show C.length ≤ (sint.Z st.minRev).toNat; omega
      have hnone : mvcc.memberBatch r' st evm = none := by
        rcases hmb with ⟨h, -⟩ | ⟨B, -, hBne, hBev⟩
        · exact h
        · exfalso
          rcases hBev with ⟨-, h⟩ | ⟨M, -, h1, h2, -⟩
          · exact hBne (by rw [h]; exact mvcc.watchEvents_empty _ _ hmCn)
          · omega
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
      obtain ⟨fv, fch, fvo, fbv, -⟩ := Hl.unsynced_facts hvWu hvST
      have fc := hcp0
      ihave Hmw := mvcc.sw_memberRes_new_synced γ σ v key r' st γw fcs evsw (sint.nat st.minRev) hM Hsr
        ⟨Hlo, by show sint.Z st.minRev ≤ ((sint.Z st.minRev).toNat : Int); omega⟩
        $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf]
      · iframe; iframe #
      ihave Hwo : mvcc.watcherOwn key st $$ [HminRev Hvict Hcomp Hrest0 Hchf]
      · iunfold mvcc.watcherOwn; iframe
      icases mvcc.sw_res_step γ σ v key r' .synced st (evsw, sint.nat st.minRev)
        $$ [$Hst $Hwo $Hmem $Hmw] with ⟨Hst, Hmem⟩
      have hok' := Hl.ok.sync_step hvWu hvST .synced st (evsw, sint.nat st.minRev)
        ⟨fc, rfl, by rw [fv]; rfl⟩
        (fun _ γw' hM' => by
          rw [show σ.M !! key = some γw from hM] at hM'; cases hM'
          have hl := HCL
          have : σ.Lmu.length = C.length := by rw [hl]
          have : (γw.lo : Int) ≤ ((sint.Z st.minRev).toNat : Int) := by omega
          simp only
          show max γw.lo σ.Lmu.length ≤ (sint.Z st.minRev).toNat
          omega)
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hm
      iexists v.step key r' .synced st (evsw, sint.nat st.minRev), PBv, PBr, key
      simp only [named]
      have e1 : (v.step key r' .synced st (evsw, sint.nat st.minRev)).Ws = <[key := r']> v.Ws := rfl
      have e2 : (v.step key r' .synced st (evsw, sint.nat st.minRev)).Wu = GMap.delete key v.Wu := rfl
      rw [e1, e2]
      iframe Hst Hmem Hsynced Hun Hvm Hbv Hrem Hwbm w s curRev compactionRev victims wb
      ipureintro
      refine ⟨Hl.step Hkey r' .synced st (evsw, sint.nat st.minRev) PBv PBr hok' Hl.bv (fun _ _ => rfl)
            (mvcc.SyncVars.settled_step Hl.ok Hl.set hvWu .synced st (evsw, sint.nat st.minRev)
              (fun _ γw' hM' => by
                have h := hmC' γw' hM'
                rw [show σ.M !! key = some γw from hM] at hM'; cases hM'
                rw [← HCL]
                simp only
                omega)
              (fun h => by simp [mvcc.SyncDst.isVictim] at h))
            (fun h => by cases h), ?_⟩
      cases self <;> rfl
    wp_apply mvcc.sw_wp_max_int64
    rw [if_pos (show sint.Z st.minRev < sint.Z (W64 ((C.length : Int) - 1) + W64 1) by
      rw [hcur1]; omega)]
    (try wp_auto)
    icases Hwbm with (%hWe | Hwbm)
    · exfalso; rw [hWe] at hW; simp at hW
    wp_apply wp_map_lookup2 $$ Hwbm as Hwbm
    ihave Hwbm : (⌜W' = ∅⌝ ∨ wb ↦$ GMap.fmap Prod.fst PB) $$ [Hwbm]
    · iright; iexact Hwbm
    have HBt : mvcc.batchOf W' STu' evm = GMap.fmap Prod.snd PB :=
      HBt.resolve_left (fun hWe => by rw [hWe] at hW; simp at hW)
    have hbk : GMap.fmap Prod.snd PB !! key = mvcc.memberBatch r' st evm := by
      rw [← HBt, mvcc.batchOf_lookup, hr, hSTuk]
    have hmb := mvcc.memberBatch_logEvents C HCwf.1 HCwf.2.1 HCwf.2.2 r' st
      (fun ev => mvcc.wgCovers W' ev.kv.key) (sint.nat minRev) C.length
      (fun ev hc => by
        simp only [mvcc.wgCovers, decide_eq_true_eq]; exact ⟨key, r', hr, hc⟩)
      (by
        have := hm2' key st hW hSTuk (by omega)
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
      obtain ⟨fv, fch, fvo, fbv, -⟩ := Hl.unsynced_facts hvWu hvST
      have fc := hcp0
      have hmN : sint.nat st.minRev ≤ C.length := by
        show (sint.Z st.minRev).toNat ≤ _; omega
      have hloN : γw.lo ≤ sint.nat st.minRev := by
        show _ ≤ (sint.Z st.minRev).toNat; omega
      ihave #Hwf' := mvcc.sw_evsWf_extend γ r' γw.lo evsw (sint.nat st.minRev) C.length C hmN
        (Nat.le_refl _) hloN $$ [$Hwf $HcertQ $HokQ $HrlC]
      rw [hwE, List.append_nil] at *
      generalize hst' : ({ st with minRev := W64 ((C.length : Int) - 1) + W64 1 } : mvcc.WatcherSt) = st'
      have hst'm : sint.Z st'.minRev = C.length := by rw [← hst']; exact hcur1
      have hn' : sint.nat st'.minRev = C.length := by
        show (sint.Z st'.minRev).toNat = _; rw [hst'm]; simp
      ihave Hmw := mvcc.sw_memberRes_new_synced γ σ v key r' st' γw fcs evsw C.length hM Hsr
        ⟨by rw [hst'm]; omega, by rw [hst'm]; exact Int.le_refl _⟩ $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf']
      · rw [hn', ← hst']; iframe; iframe #
      ihave Hwo : mvcc.watcherOwn key st' $$ [HminRev Hvict Hcomp Hrest0 Hchf]
      · rw [← hst']; iunfold mvcc.watcherOwn; iframe
      icases mvcc.sw_res_step γ σ v key r' .synced st' (evsw, C.length) $$ [$Hst $Hwo $Hmem $Hmw]
        with ⟨Hst, Hmem⟩
      have hok' := Hl.ok.sync_step hvWu hvST .synced st' (evsw, C.length)
        ⟨by rw [← hst']; exact fc, by rw [← hst'], by rw [← hst']; exact fv⟩
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
      refine ⟨Hl.step Hkey r' .synced st' (evsw, C.length) PBv PBr hok' Hl.bv (fun _ _ => rfl)
            (mvcc.SyncVars.settled_step Hl.ok Hl.set hvWu .synced st' (evsw, C.length)
              (fun _ _ _ => Or.inl (Nat.le_of_eq (congrArg List.length HCL)))
              (fun h => by simp [mvcc.SyncDst.isVictim] at h))
            (fun h => by cases h), ?_⟩
      cases self <;> rfl
    · rw [hsome, GMap.lookup_fmap] at hbk
      obtain ⟨ebp, hPBk⟩ : ∃ ebp, PB !! key = some (ebp, B) := by
        cases h : PB !! key with
        | none => rw [h] at hbk; cases hbk
        | some p =>
          rw [h] at hbk; obtain ⟨p1, p2⟩ := p; simp at hbk; exact ⟨p1, by rw [hbk]⟩
      rw [hPBk]
      simp only [Option.map_some, Option.getD_some, Option.isSome_some, _root_.decide_true,
        Bool.not_true]
      have hPBrk : PBr !! key = some (ebp, B) := hPBr.trans hPBk
      icases (BigSepM.bigSepM_delete (by rw [gmap_get?_eq]; exact hPBrk)).1 $$ Hrem
        with ⟨⟨%Hebnn, HB⟩, Hrem⟩
      iunfold mvcc.ownEventBatch at HB
      icases HB with ⟨%sl, %eps, Heb, Hsl, Hcap, %Heplen, #HevB⟩
      simp only at Heplen ⊢
      obtain ⟨fv, fch, fvo, fbv, -⟩ := Hl.unsynced_facts hvWu hvST
      have fc := hcp0
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
          (Nat.le_refl _) hloN $$ [$Hwf $HcertQ $HokQ $HrlC]
        rw [← hevB]
        have hmodB := mvcc.watchEvents_modRev C HCwf.2.1 r' (sint.nat st.minRev) C.length
          (Nat.le_refl _)
        rw [← hevB] at hmodB
        wp_apply (hSend γ key γw r' fcs st.ch 1 (1 : Qp).half evsw C.length _ eps B.evs (DFrac.own 1) [] 1 none iprop(True))
          $$ [Hchf Hlv Ha Hsl] as %b ⟨Hchf, Hlv, Hsl, Ha, -, -, -⟩
        · rw [if_neg hBne]
          iframe Hmeta Hfx Hfo Hch Hchf Hlv Ha Hwf' Hsl HevB
          isplitr
          · iapply mvcc.covPre_nil
          isplitr
          · iapply mvcc.covAuth_nil
          isplitr
          · iapply mvcc.notifiedLent_none
          isplitr
          · ipureintro; intro h; exact absurd h hBne
          isplitr
          · ipureintro; intro h; exact absurd h hBne
          isplitr
          · itrivial
          isplitr
          · ileft; ipureintro; rfl
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
              ⟨fun h => absurd hmr0 h, fun ev hev => by
                have := hmodB ev hev
                have : (sint.nat st.minRev : Int) = sint.Z st.minRev := by
                  show ((sint.Z st.minRev).toNat : Int) = _; omega
                rw [hst'm]; omega⟩, hBne⟩
            $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf']
          · rw [← hst']; iframe; iframe #
          ihave Hwo : mvcc.watcherOwn key st' $$ [HminRev Hvict Hcomp Hrest0 Hchf]
          · rw [← hst']; iunfold mvcc.watcherOwn; iframe
          icases mvcc.sw_res_step γ σ v key r' (.victim B) st' (evsw, C.length)
            $$ [$Hst $Hwo $Hmem $Hmw] with ⟨Hst, Hmem⟩
          have hok' := Hl.ok.sync_step hvWu hvST (.victim B) st' (evsw, C.length)
            ⟨by rw [← hst']; exact fc, by rw [← hst'], by rw [← hst']; rfl⟩
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
              exact GMap.lookup_delete_ne _ (Ne.symm hk))
            (mvcc.SyncVars.settled_step Hl.ok Hl.set hvWu (.victim B) st' (evsw, C.length)
              (fun h => by cases h)
              (fun _ => by have h := hst'm; rw [HCL] at h; simp only; omega))
            (fun h => by cases h), ?_⟩
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
          have hn' : sint.nat st'.minRev = C.length := by
            show (sint.Z st'.minRev).toNat = _; rw [hst'm]; simp
          ihave Hmw := mvcc.sw_memberRes_new_synced γ σ v key r' st' γw fcs (evsw ++ B.evs) C.length
            hM Hsr ⟨by rw [hst'm]; omega, by rw [hst'm]; exact Int.le_refl _⟩
            $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf']
          · rw [hn', ← hst']; iframe; iframe #
          ihave Hwo : mvcc.watcherOwn key st' $$ [HminRev Hvict Hcomp Hrest0 Hchf]
          · rw [← hst']; iunfold mvcc.watcherOwn; simp only [fv]; iframe
          icases mvcc.sw_res_step γ σ v key r' .synced st' (evsw ++ B.evs, C.length)
            $$ [$Hst $Hwo $Hmem $Hmw] with ⟨Hst, Hmem⟩
          have hok' := Hl.ok.sync_step hvWu hvST .synced st' (evsw ++ B.evs, C.length)
            ⟨by rw [← hst']; exact fc, by rw [← hst'], by rw [← hst']; exact fv⟩
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
              exact GMap.lookup_delete_ne _ (Ne.symm hk))
            (mvcc.SyncVars.settled_step Hl.ok Hl.set hvWu .synced st' (evsw ++ B.evs, C.length)
              (fun _ _ _ => Or.inl (Nat.le_of_eq (congrArg List.length HCL)))
              (fun h => by simp [mvcc.SyncDst.isVictim] at h))
            (fun h => by cases h), ?_⟩
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
          (by omega) hloN $$ [$Hwf $HcertQ $HokQ $HrlC]
        rw [← hevB]
        have hmodB := mvcc.watchEvents_modRev C HCwf.2.1 r' (sint.nat st.minRev) M
          (by omega)
        rw [← hevB] at hmodB
        wp_apply (hSend γ key γw r' fcs st.ch 1 (1 : Qp).half evsw M _ eps B.evs (DFrac.own 1) [] 1 none iprop(True))
          $$ [Hchf Hlv Ha Hsl] as %b ⟨Hchf, Hlv, Hsl, Ha, -, -, -⟩
        · rw [if_neg hBne]
          iframe Hmeta Hfx Hfo Hch Hchf Hlv Ha Hwf' Hsl HevB
          isplitr
          · iapply mvcc.covPre_nil
          isplitr
          · iapply mvcc.covAuth_nil
          isplitr
          · iapply mvcc.notifiedLent_none
          isplitr
          · ipureintro; intro h; exact absurd h hBne
          isplitr
          · ipureintro; intro h; exact absurd h hBne
          isplitr
          · itrivial
          isplitr
          · ileft; ipureintro; rfl
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
              ⟨fun _ => by rw [← hst'], fun ev hev => by
                have := hmodB ev hev
                have : (sint.nat st.minRev : Int) = sint.Z st.minRev := by
                  show ((sint.Z st.minRev).toNat : Int) = _; omega
                rw [hst'm]; omega⟩, hBne⟩
            $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf']
          · rw [← hst']; iframe; iframe #
          ihave Hwo : mvcc.watcherOwn key st' $$ [HminRev Hvict Hcomp Hrest0 Hchf]
          · rw [← hst']; iunfold mvcc.watcherOwn; iframe
          icases mvcc.sw_res_step γ σ v key r' (.victim B) st' (evsw, M)
            $$ [$Hst $Hwo $Hmem $Hmw] with ⟨Hst, Hmem⟩
          have hok' := Hl.ok.sync_step hvWu hvST (.victim B) st' (evsw, M)
            ⟨by rw [← hst']; exact fc, by rw [← hst'], by rw [← hst']; rfl⟩
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
              exact GMap.lookup_delete_ne _ (Ne.symm hk))
            (mvcc.SyncVars.settled_step Hl.ok Hl.set hvWu (.victim B) st' (evsw, M)
              (fun h => by cases h)
              (fun _ => by
                have hle : M ≤ C.length := by omega
                rw [HCL] at hle; simp only; omega))
            (fun h => by cases h), ?_⟩
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
              show M = (sint.Z st'.minRev).toNat; rw [hst'm]; simp⟩
            (by show (sint.Z st'.minRev).toNat ≤ max γw.lo C.length; rw [hst'm]; simp; omega)
            (by rw [← hst']; exact hcp0)
            $$ [Hmeta Hfx Hch Hfo Ha Hlv Hwf']
          · rw [← hst']; iframe; iframe #
          ihave Hwo : mvcc.watcherOwn key st' $$ [HminRev Hvict Hcomp Hrest0 Hchf]
          · rw [← hst']; iunfold mvcc.watcherOwn; simp only [fv]; iframe
          icases mvcc.sw_res_step γ σ v key r' .unsynced st' (evsw ++ B.evs, M)
            $$ [$Hst $Hwo $Hmem $Hmw] with ⟨Hst, Hmem⟩
          have hok' := Hl.ok.sync_step hvWu hvST .unsynced st' (evsw ++ B.evs, M)
            ⟨by rw [← hst']; exact fc, by rw [← hst'], by rw [← hst']; exact fv⟩
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
              exact GMap.lookup_delete_ne _ (Ne.symm hk))
            (mvcc.SyncVars.settled_step Hl.ok Hl.set hvWu .unsynced st' (evsw ++ B.evs, M)
              (fun h => by cases h)
              (fun h => by simp [mvcc.SyncDst.isVictim] at h))
            (fun _ => by rw [hst'm, ← HCL]; omega), ?_⟩
          exact hm'

  isplitr
  · imodintro
    iintro %i %key %m' ⟨%Hkey, %Hu⟩ HP
    iNamed HP
    exfalso
    obtain ⟨Hl, hm'⟩ := Hi
    have hnot := not_mem_take_of_nodup Hknodup Hkey
    have hW : (W' !! key).isSome := by
      have := (Hkset key).1 (List.mem_of_getElem? Hkey)
      rw [GMap.domSet, GMap.lookup_fmap] at this; simpa using this
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hW
    obtain ⟨-, hu, -⟩ := Hl.rest key hnot
    subst hm'
    cases hs : self
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, GMap.domSet, GMap.lookup_fmap, hr] at Hu
      cases Hu
    · have hu' : v.Wu !! key = some r := hu.trans (hW'Wu1 key r hr)
      simp only [hs, ↓reduceIte, GMap.domSet, GMap.lookup_fmap, hu'] at Hu
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
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HrevQ HclogQ HbucketQ HtoksQ HlogQ HcmpQ HcrevQ HrstR]
    as HrevMuR
  · inext
    have ecr : mvcc.crevUB (GF := GF) { γ.st.idx with nev := p.nev, cmp := p.cmp }
        sync.rfrac.half.half cQ = mvcc.crevUB γ.st.idx sync.rfrac.half.half cQ :=
      mvcc.crevUB_withPhys γ.st p _ _
    irevert HcrevQ; rw [ecr]; iintro HcrevQ
    iapply mvcc.revMuInv_close; iframe HrstR; iunfold mvcc.revMuBody
    iexists C, ntok, cQ
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨HneQ, HbudgetQ, HcQ⟩
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
  ihave #Hwfz2 := mvcc.wsWatchFrozen_mono γ σ σf (fun h => by first | exact h | simpa using h) $$ Hwfz
  ihave HPf : mvcc.watchStoreBody s γ 1 σf $$ [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo
      Hmeta Hwt Hmem]
  · iunfold mvcc.watchStoreBody
    simp only [named]
    iframe Hσ Hwlog Hcert Hwfz2 Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmfix
    isplitr
    · ipureintro; exact hlen'
    isplitl [Hmem]
    · iapply (BigSepM.bigSepM_mono (fun {k x} _ => ?_)) $$ Hmem
      rw [mvcc.sw_memberRes_congr γ 1 (v.st σ) σf k x rfl rfl rfl rfl (hvo k).symm rfl]
    isplitr
    · iapply (BigSepM.bigSepM_mono (fun {k x} _ => by unfold mvcc.outRes; exact .rfl)) $$ Hout
    ipureintro; exact hokf
  ihave Hwsf : mvcc.fieldShare st γ.st (1 : Qp).half.half $$ [Hcur Hfb Hfidx Hfsch Hfstop Hfrst]
  · iunfold mvcc.fieldShare; iexists p, o
    iunfold mvcc.fieldShareAt
    simp only [named]
    iframe Hcur Hfrst Hph
    iunfold mvcc.storeFields; simp only [named]; iframe Hfb Hfidx Hfsch Hfstop
  ihave Hwsf : mvcc.wsFields s γ 1 $$ [Hwsf Hwsd]
  · iunfold mvcc.wsFields; iexists st; iframe Hstp Hwsf Hwsd
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl HPf Hrel Hwsf]
  · inext; iunfold mvcc.watchStoreInv; iexists σf; iframe HPf Hrel Hwsf; ipureintro
    refine ⟨mvcc.WsState.settled_congr Hl.set rfl rfl rfl rfl rfl rfl hvo, Hsrb, ?_⟩
    -- (D22 receiver epochs, S6) the unsynced members kept are below the notified log, the others
    -- untouched (not chosen: no reset)
    intro k stk hu hst
    by_cases hk : k ∈ keys
    · left
      exact Hl.uns k stk (by rw [List.take_length]; exact hk) hu hst
    · obtain ⟨h1, h2, -⟩ := Hl.rest k (by rw [List.take_length]; exact hk)
      have hst' : ST0 !! k = some stk := by rw [← h1]; exact hst
      have hu1 : (Wu1 !! k).isSome := by
        have e : v.Wu !! k = Wu1 !! k := h2
        rw [← e]; exact hu
      have hu' : (σ.Wu !! k).isSome := by
        rcases hWu1 k with e | ⟨-, e⟩
        · rw [← e]; exact hu1
        · rw [e] at hu1; cases hu1
      rw [hST0] at hst'
      cases h0 : σ.ST !! k with
      | none => rw [h0] at hst'; cases hst'
      | some st0 =>
        rw [h0] at hst'
        simp only [Option.map_some, Option.some.injEq] at hst'
        subst hst'
        by_cases hc : (Cm !! k).isSome
        · -- (watches across a compaction) sent the compaction response, kept unsynced (the copy
          -- branch): behind the compaction revision, so below the notified log
          left
          obtain ⟨-, st1, hst1, hlt⟩ := hCm k hc
          rw [hSTu, if_pos hu', h0] at hst1; cases hst1
          rw [mvcc.chooseF_minRev]; rw [hcQ] at hlt
          show _ < (σ.Lmu.length : Int)
          rw [← HCL]; have := HcQ.2; omega
        · have hd : (domSet W0 !! k).isSome = false := by
            cases h : (domSet W0 !! k).isSome
            · rfl
            · exfalso; apply hk; apply (Hkset k).2
              have hk0 : (W0 !! k).isSome := by
                rw [GMap.domSet, GMap.lookup_fmap] at h; simpa using h
              obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 hk0
              rw [GMap.domSet, GMap.lookup_fmap, ← hW'D, mvcc.sw_filter_lookup, hr0]
              simp [hc]
          rw [mvcc.chooseF_of _ _ _ _ _ hd (by simpa using hc)]
          exact Hurst k st0 hu' h0
  (try wp_auto)
  iapply HΦ
  iunfold mvcc.watchReader
  iframe Hmur
  iunfold mvcc.storeReader; iunfold mvcc.storeReaderC
  simp only [named]
  iframe

end proof
end EtcdGrove
end Perennial
