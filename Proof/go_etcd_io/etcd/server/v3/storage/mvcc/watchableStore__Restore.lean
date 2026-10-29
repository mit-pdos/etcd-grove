/-
Proof of the spec of the same name (D22 receiver epochs, S6). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__add
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherGroup

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace mvcc

/-- A watcher's state with its restore flag set (`wa.restore = true`). -/
def setRestore (st : WatcherSt) : WatcherSt := { st with restore := true }

/-- **The lock's state after `watchableStore.Restore`** at the restored log `Lr`: no synced
watcher, every synced one unsynced with its `restore` flag set and delivered up to its `minRev`
(as far as its events go: the synced `popFacts`), the rest as before. -/
def WsState.restoreSt (σ : WsState) (Lr : Log) : WsState where
  Lmu := Lr
  Ws := ∅
  Wu := σ.Wu ∪ σ.Ws
  ST := gmapMapK (fun w st => if (σ.Ws !! w).isSome then setRestore st else st) σ.ST
  Wo := σ.Wo
  M := σ.M
  E := gmapMapK (fun w e => if (σ.Ws !! w).isSome then
    (e.1, ((σ.ST !! w).map (fun st => sint.nat st.minRev)).getD e.2) else e) σ.E
  vs := σ.vs
  vbs := σ.vbs
  VB := σ.VB

section pure
variable (σ : WsState) (Lr : Log)

theorem WsState.restoreSt_victimOf (w : Loc) : (σ.restoreSt Lr).victimOf w = σ.victimOf w := rfl

theorem WsState.restoreSt_Wu (w : Loc) : (σ.restoreSt Lr).Wu !! w = (σ.Wu !! w).or (σ.Ws !! w) := by
  show (σ.Wu ∪ σ.Ws) !! w = _; rw [GMap.lookup_union]

theorem WsState.restoreSt_ST (w : Loc) : (σ.restoreSt Lr).ST !! w =
    (σ.ST !! w).map (fun st => if (σ.Ws !! w).isSome then setRestore st else st) := rfl

theorem WsState.restoreSt_E (w : Loc) : (σ.restoreSt Lr).E !! w =
    (σ.E !! w).map (fun e => if (σ.Ws !! w).isSome then
      (e.1, ((σ.ST !! w).map (fun st => sint.nat st.minRev)).getD e.2) else e) := rfl

theorem WsState.restoreSt_live (w : Loc) : (σ.restoreSt Lr).live w ↔ σ.live w := by
  unfold WsState.live
  rw [WsState.restoreSt_Wu, WsState.restoreSt_victimOf]
  show ((∅ : GMap Loc WatchRange) !! w).isSome = true ∨ _ ↔ _
  cases (σ.Ws !! w) <;> cases (σ.Wu !! w) <;> simp

/-- The lock's facts after the restore. -/
theorem WsOk.restoreSt {σ : WsState} (h : WsOk σ) (Lr : Log) : WsOk (σ.restoreSt Lr) := by
  have hl := WsState.restoreSt_live σ Lr
  have hST : ∀ w, ((σ.restoreSt Lr).ST !! w).isSome = (σ.ST !! w).isSome := by
    intro w; rw [WsState.restoreSt_ST]; cases σ.ST !! w <;> rfl
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, h.v_one, fun w hw => ?_, fun w => ?_,
    fun w hw => ?_, h.wo_m, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w st hs => ?_,
    h.wo_flags, fun w γw ed hw => ?_⟩
  · simp [WsState.restoreSt] at hw
  · simp [WsState.restoreSt] at hw
  · rw [WsState.restoreSt_victimOf]
    rw [WsState.restoreSt_Wu] at hw
    cases hu : σ.Wu !! w with
    | some _ => exact h.wu_v w (by rw [hu]; rfl)
    | none => rw [hu] at hw; exact h.ws_v w (by simpa using hw)
  · rw [hST]; exact h.live_st w ((hl w).1 hw)
  · rw [WsState.restoreSt_E, hl]
    have := h.live_e w
    cases he : σ.E !! w <;> simp_all
  · rw [hST] at hw; exact h.st_m w hw
  · rw [hST]; exact h.m_st w hw
  · rw [WsState.restoreSt_ST, h.wo_st w hw]; rfl
  · rw [hl]; exact h.wo_live w hw
  · rw [WsState.restoreSt_ST] at hs
    cases h0 : σ.ST !! w with
    | none => rw [h0] at hs; cases hs
    | some st0 =>
      rw [h0] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      obtain ⟨f1, f2, f3⟩ := h.st_flags w st0 h0
      have e1 : st.compacted = st0.compacted := by rw [← hs]; split <;> rfl
      have e2 : st.victim = st0.victim := by rw [← hs]; split <;> rfl
      have e3 : st.ch = st0.ch := by rw [← hs]; split <;> rfl
      refine ⟨by rw [e1]; exact f1, fun hlv => ?_, by rw [e3, hl]; exact f3⟩
      rw [e2, WsState.restoreSt_victimOf]; exact f2 ((hl w).1 hlv)
  · simp [WsState.restoreSt] at hw

/-- Settled after the restore (no synced watcher; the victims below a longer log). -/
theorem WsState.restoreSt_settled {σ : WsState} (hs : σ.settled) (Lr : Log)
    (hL : σ.Lmu.length ≤ Lr.length) : (σ.restoreSt Lr).settled := by
  refine ⟨fun w γw ed hw => by simp [WsState.restoreSt] at hw, fun w st h1 hst => ?_,
    fun w st h2 => ?_⟩
  · rw [WsState.restoreSt_victimOf] at h1
    rw [WsState.restoreSt_ST] at hst
    cases h0 : σ.ST !! w with
    | none => rw [h0] at hst; cases hst
    | some st0 =>
      rw [h0] at hst
      simp only [Option.map_some, Option.some.injEq] at hst
      have e : st.minRev = st0.minRev := by rw [← hst]; split <;> rfl
      rw [e]
      have := hs.2.1 w st0 h1 h0
      show sint.Z st0.minRev ≤ (Lr.length : Int); omega
  · have := hs.2.2 w st h2
    show sint.Z st.minRev ≤ (Lr.length : Int); omega

theorem WsState.restoreSt_srBelow {σ : WsState} (hs : σ.srBelow σ.Lmu.length) (Lr : Log)
    (hL : σ.Lmu.length ≤ Lr.length) : (σ.restoreSt Lr).srBelow (σ.restoreSt Lr).Lmu.length := by
  intro w γw hm hn
  have := hs w γw hm hn
  show γw.lo ≤ Lr.length; omega

theorem WsState.restoreSt_unsRst {σ : WsState} (hs : σ.unsRst) (Lr : Log)
    (hL : σ.Lmu.length ≤ Lr.length) : (σ.restoreSt Lr).unsRst := by
  intro w st hu hst
  rw [WsState.restoreSt_ST] at hst
  cases h0 : σ.ST !! w with
  | none => rw [h0] at hst; cases hst
  | some st0 =>
    rw [h0] at hst
    simp only [Option.map_some, Option.some.injEq] at hst
    by_cases hw : (σ.Ws !! w).isSome
    · rw [ite_eq_left hw] at hst; subst hst; right; rfl
    · rw [ite_eq_right hw] at hst; subst hst
      have hu' : (σ.Wu !! w).isSome := by
        rw [WsState.restoreSt_Wu] at hu
        cases h1 : σ.Wu !! w with
        | some _ => rfl
        | none => rw [h1] at hu; simp at hu; exact absurd hu hw
      rcases hs w st0 hu' h0 with h | h
      · left; show sint.Z st0.minRev < (Lr.length : Int); omega
      · right; exact h

end pure

end mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A watcher's resources across the restore**: a synced one becomes unsynced delivered up to its
`minRev` (its events up to there are its delivered ones, the synced `popFacts`: no event is
delivered or dropped; its `minRev` at most its first revision or the notified log's length, under
whose certificate), the others unchanged. -/
theorem mvcc.memberRes_restoreSt (γ : mvcc.WsNames) (σ : mvcc.WsState) (hset : σ.settled)
    (Lr : mvcc.Log) (w : Loc) (st : mvcc.WatcherSt) (hst : σ.ST !! w = some st) :
    mvcc.memberRes (GF := GF) γ 1 σ w st ∗ mvcc.idxCert γ.st.idx σ.Lmu ⊢
      mvcc.memberRes γ 1 (σ.restoreSt Lr) w
        (if (σ.Ws !! w).isSome then mvcc.setRestore st else st) := by
  by_cases hws : (σ.Ws !! w).isSome
  · rw [ite_eq_left hws]
    have hl : σ.live w := Or.inl hws
    have hl' : (σ.restoreSt Lr).live w := (mvcc.WsState.restoreSt_live σ Lr w).2 hl
    have hws' : ((σ.restoreSt Lr).Ws !! w).isSome = false := rfl
    have hwu' : ((σ.restoreSt Lr).Wu !! w).isSome = true := by
      rw [mvcc.WsState.restoreSt_Wu]; cases h : σ.Wu !! w <;> simp_all
    have hE' : ∀ e, σ.E !! w = some e →
        (σ.restoreSt Lr).E !! w = some (e.1, sint.nat st.minRev) := by
      intro e he; rw [mvcc.WsState.restoreSt_E, he, hst]; simp [hws]
    have hch : (mvcc.setRestore st).ch = st.ch := rfl
    have hmr : (mvcc.setRestore st).minRev = st.minRev := rfl
    unfold mvcc.memberRes mvcc.popFacts
    simp only [hl, hl', hws, hws', hwu', ↓reduceIte, Bool.false_eq_true, hch, hmr]
    iintro ⟨⟨%γw, %r, %fcs, %hM, #Hm, #Hf, #Hc, #Hfo, %Hsr, %evsw, %d, %hE, Ha, Hl,
      ⟨%Hp, #Hwf, #Hwm⟩⟩, #Hcert⟩
    iexists γw, r, fcs
    iframe Hm Hf Hc Hfo Ha Hl Hwm
    isplitr
    · ipureintro; exact hM
    isplitr
    · ipureintro; exact Hsr
    isplitr
    · ipureintro; exact hE' _ hE
    isplitr
    · ipureintro; exact ⟨Hp.1, rfl⟩
    iexists σ.Lmu
    iframe Hcert
    ipureintro
    have hb := hset.1 w γw (evsw, d) hws hM hE
    simp only at hb
    show (sint.Z st.minRev).toNat ≤ _
    omega
  · have hws0 : σ.Ws !! w = none := by
      cases h : σ.Ws !! w with
      | none => rfl
      | some _ => rw [h] at hws; exact absurd rfl hws
    rw [ite_eq_right hws]
    iintro ⟨H, -⟩
    iapply mvcc.memberRes_congr γ 1 σ (σ.restoreSt Lr) w st rfl
      (by show ((∅ : GMap Loc mvcc.WatchRange) !! w).isSome = _; rw [hws0]; rfl)
      (by rw [mvcc.WsState.restoreSt_Wu, hws0]; cases σ.Wu !! w <;> rfl) rfl
      (by rw [mvcc.WsState.restoreSt_E]; cases σ.E !! w <;> simp [hws])
    iexact H

/-- The unsynced group with the first `n` synced watchers of `keys` added. -/
theorem mvcc.rs_union_insert (Wu T : GMap Loc mvcc.WatchRange) (k : Loc) (r : mvcc.WatchRange)
    (h : Wu !! k = none) : <[k := r]> (Wu ∪ T) = Wu ∪ <[k := r]> T := by
  refine GMap.ext (fun x => ?_)
  show (<[k := r]> (Wu ∪ T)) !! x = (Wu ∪ <[k := r]> T) !! x
  by_cases hx : k = x
  · subst hx; rw [GMap.lookup_insert, GMap.lookup_union, h, GMap.lookup_insert]; rfl
  · rw [GMap.lookup_insert_ne _ _ hx, GMap.lookup_union, GMap.lookup_union,
      GMap.lookup_insert_ne _ _ hx]

/-- `s.Restore(b')` of the watchable store (`watchable_store.go:207-220`): `store.Restore` (its axiom)
under the lock, every synced watcher moved to the unsynced group with its restore flag set, the
synced group fresh; the lock's state the restored one (`WsState.restoreSt`). -/
theorem mvcc.watchableStore.Restore.wp_proof
    (hRestore : mvcc.store.Restore.spec (GF := GF) (hG := hG))
    (hNew : mvcc.newWatcherGroup.spec (GF := GF) (hG := hG))
    (hAdd : mvcc.watcherGroup.add.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.Restore.spec (GF := GF) (hG := hG) := by
  have hAddG := mvcc.watcherGroup.add.spec_group hAdd
  intro s st γ b' d' γb' P' L R hLR hR
  wp_start as ⟨#Hws, %Hkb, %Hcm', Hcl, Hfrag, Hown, #Hfrz, Hww, #Hok', #HbkT, #HcrT, Hview, Hnc, Hrr, Hrts⟩
  ihave #HwsAll : mvcc.isWatchableStore s st γ $$ []
  · iexact Hws
  ihave #Hpkg0 : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
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
  -- the sole writer's notified log is the lock's
  iunfold mvcc.watchWriter at Hww
  icases Hww with ⟨#HcL, Htoks, HwlW⟩
  iunfold mvcc.wlogQ at Hwlog
  icases Hwlog with ⟨HwlL, HlogQ⟩
  ihave %HLL := monoListAuthOwn_agree γ.wlog _ _ _ _ $$ HwlW HwlL
  obtain ⟨-, HLL⟩ := HLL
  -- the lock's share of the inner store's fields and its deposit (D22 receiver epochs, S5a/S5b)
  iunfold mvcc.wsFields at Hwsf
  icases Hwsf with ⟨%st', #Hst', Hfs, Hwsd⟩
  ihave #Hstp : s.[watchableStore, go!"store"] ↦□ st $$ []
  · iunfold mvcc.isWatchableStore at HwsAll; iNamed HwsAll; iexact Hst
  icombine Hstp Hst' gives %Hsteq
  subst Hsteq
  -- `s.store.Restore(b)`
  (try wp_auto)
  wp_apply (hRestore st γ.st b' d' γb' P' L R hLR hR) $$ [Hcl Hfs Hwsd Hfrag Hown Htoks HlogQ
      Hview Hnc Hrr Hrts]
    as ⟨%p', %Hp', Hcl, Hfs, Hwsd, Hfrag, Hown, #HhP, #HcL', Htoks, HlogQ, Hold, Hnew'⟩
  · simp only [mvcc.wBudget, Hwq, ↓reduceIte]
    iframe Hcl Hfs Hfrag Hown Htoks Hview Hnc Hrr Hrts
    iframe #
    isplitr
    · ipureintro; exact Hkb
    isplitr
    · ipureintro; exact Hcm'
    isplitl [Hwsd]
    · iunfold mvcc.wsDep; iexact Hwsd
    iunfold mvcc.logQ
    rw [HLL]; iexact HlogQ
  simp only [Hwq, ↓reduceIte]
  obtain ⟨hbk', hkb'⟩ := Hp'
  generalize hL' : ([[], []] ++ R : mvcc.Log) = L' at *
  have hLL' : σ.Lmu.length ≤ L'.length := by rw [← HLL]; exact hLR.length_le
  (try wp_auto)
  -- the synced watchers, to the unsynced group with their restore flag set
  icases mvcc.ownWatcherGroup_fixed (mvcc.syncedAddr s) σ.Ws $$ Hsynced with ⟨Hsynced, #Hfx⟩
  icases mvcc.ownWatcherGroup_watchers (mvcc.syncedAddr s) σ.Ws $$ Hsynced with ⟨%v, Hwg, Hwss, Hback⟩
  iunfold mvcc.ownWatcherSet at Hwss
  (try wp_auto)
  let STi : List Loc → Nat → GMap Loc mvcc.WatcherSt := fun keys n =>
    mvcc.gmapMapK (fun w x => if w ∈ keys.take n then mvcc.setRestore x else x) σ.ST
  have hSTi : ∀ keys n w, STi keys n !! w =
      (σ.ST !! w).map (fun x => if w ∈ keys.take n then mvcc.setRestore x else x) := fun _ _ _ => rfl
  have hWsdom : ∀ k, (domSet σ.Ws !! k).isSome ↔ (σ.Ws !! k).isSome := by
    intro k; rw [GMap.domSet, GMap.lookup_fmap]; cases σ.Ws !! k <;> simp
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List Loc) (i : Int) => iprop(∃ (wv : Loc),
      "wa" ∷ wa_ptr ↦ wv ∗ "s" ∷ s_ptr ↦ s ∗
      "Hun" ∷ mvcc.ownWatcherGroup (mvcc.unsyncedAddr s) (σ.Wu ∪ mvcc.takeMembers σ.Ws keys i.toNat) ∗
      "Hst" ∷ ([∗map] w ↦ x ∈ STi keys i.toNat, mvcc.watcherOwn w x) ∗
      "%Hi" ∷ ⌜0 ≤ i⌝)) $$ Hwss
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [wa s Hunsynced Hst]
  · iexists _
    simp only [named]
    iframe wa s
    have h0 : STi keys (0 : Int).toNat = σ.ST := by
      refine GMap.ext (fun k => ?_)
      show STi keys 0 !! k = σ.ST !! k
      rw [hSTi]; cases σ.ST !! k <;> simp
    have h1 : σ.Wu ∪ mvcc.takeMembers σ.Ws keys (0 : Int).toNat = σ.Wu := by
      rw [show (0 : Int).toNat = 0 from rfl, mvcc.takeMembers_zero]
      refine GMap.ext (fun k => ?_)
      show (σ.Wu ∪ ∅) !! k = σ.Wu !! k
      rw [GMap.lookup_union]; cases σ.Wu !! k <;> rfl
    rw [h0, h1]
    iframe Hunsynced Hst
    ipureintro; exact Int.le_refl _
  isplitr
  · imodintro
    iintro %i %key %u ⟨%Hkey, %Hu⟩ HP
    iNamed HP
    have hnot := not_mem_take_of_nodup Hknodup Hkey
    have hW : (σ.Ws !! key).isSome := (hWsdom key).1 (by rw [Hu]; rfl)
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hW
    obtain ⟨st0, hst0⟩ := Option.isSome_iff_exists.1 (Hok.live_st key (Or.inl hW))
    have hwu0 : σ.Wu !! key = none := Hok.ws_wu key hW
    obtain ⟨hT, hN⟩ := mvcc.takeMembers_succ σ.Ws keys i.toNat key r Hkey Hknodup hr
    have hsti : STi keys i.toNat !! key = some st0 := by
      rw [hSTi, hst0]; simp [hnot]
    have hstep : Iris.Std.PartialMap.insert (STi keys i.toNat) key (mvcc.setRestore st0) =
        STi keys (i + 1).toNat := by
      refine GMap.ext (fun k => ?_)
      show (<[key := mvcc.setRestore st0]> (STi keys i.toNat)) !! k = STi keys (i + 1).toNat !! k
      have htk : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
      rw [hSTi, htk]
      by_cases hk : key = k
      · subst hk; rw [GMap.lookup_insert, hst0]; simp
      · rw [GMap.lookup_insert_ne _ _ hk, hSTi]
        have : (k ∈ keys.take i.toNat ++ [key]) ↔ k ∈ keys.take i.toNat := by
          simp [Ne.symm hk]
        simp only [this]
    icases (BigSepM.bigSepM_insert_acc (show Iris.Std.PartialMap.get? (STi keys i.toNat) key = some st0
      from hsti)) $$ Hst with ⟨Hw, Hst⟩
    iunfold mvcc.watcherOwn at Hw
    icases Hw with ⟨Hmin, Hvic, Hcomp, Hres, Hch⟩
    icases (BigSepM.bigSepM_lookup_acc (m := σ.Ws) (by rw [gmap_get?_eq]; exact hr)).1 $$ Hfx
      with ⟨⟨%fcs, #Hf⟩, -⟩
    (try wp_auto)
    wp_apply (hAddG (mvcc.unsyncedAddr s) (σ.Wu ∪ mvcc.takeMembers σ.Ws keys i.toNat) key r fcs)
      $$ [$Hun $Hf] as Hun
    · ipureintro
      refine ⟨by rw [GMap.lookup_union, hwu0, hN]; rfl, ?_⟩
      have hsz : GMap.size (σ.Wu ∪ mvcc.takeMembers σ.Ws keys i.toNat) ≤ GMap.size σ.M :=
        mvcc.gmap_size_le_of_dom _ _ (fun w hw => by
          rw [GMap.lookup_union] at hw
          cases hu : σ.Wu !! w with
          | some _ => exact Hok.st_m w (Hok.live_st w (Or.inr (Or.inl (by rw [hu]; rfl))))
          | none =>
            rw [hu] at hw
            simp only [Option.none_or] at hw
            have hw' : (σ.Ws !! w).isSome := by
              obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hw
              rw [GMap.lookup_weaken hx (mvcc.takeMembers_subseteq _ _ _)]; rfl
            exact Hok.st_m w (Hok.live_st w (Or.inl hw')))
      omega
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key
    simp only [named]
    iframe wa s
    isplitl [Hun]
    · rw [show (i + 1).toNat = i.toNat + 1 by omega, hT, ← mvcc.rs_union_insert _ _ _ _ hwu0]
      iexact Hun
    isplitl [Hst Hmin Hvic Hcomp Hres Hch]
    · rw [← hstep]
      iapply Hst
      iunfold mvcc.watcherOwn
      iframe
    ipureintro; omega
  iintro HP Hwss
  iNamed HP
  have hall : keys.take (GMap.size (domSet σ.Ws) : Int).toNat = keys := by
    rw [show ((GMap.size (domSet σ.Ws) : Nat) : Int).toNat = keys.length by omega, List.take_length]
  have hTfin : mvcc.takeMembers σ.Ws keys (GMap.size (domSet σ.Ws) : Int).toNat = σ.Ws := by
    refine GMap.ext (fun k => ?_)
    show mvcc.takeMembers σ.Ws keys _ !! k = σ.Ws !! k
    unfold mvcc.takeMembers
    rw [GMap.lookup_filter, hall]
    cases h : σ.Ws !! k with
    | none => rfl
    | some r => simp [(Hkset k).2 ((hWsdom k).2 (by rw [h]; rfl))]
  have hSTfin : STi keys (GMap.size (domSet σ.Ws) : Int).toNat = (σ.restoreSt L').ST := by
    refine GMap.ext (fun k => ?_)
    show STi keys _ !! k = (σ.restoreSt L').ST !! k
    rw [hSTi, hall, mvcc.WsState.restoreSt_ST]
    cases σ.ST !! k with
    | none => rfl
    | some x =>
      simp only [Option.map_some, Option.some.injEq]
      by_cases hk : (σ.Ws !! k).isSome
      · rw [if_pos ((Hkset k).2 ((hWsdom k).2 hk)), if_pos hk]
      · rw [if_neg (fun h => hk ((hWsdom k).1 ((Hkset k).1 h))), if_neg hk]
  rw [hTfin, hSTfin]
  -- the synced group fresh
  ihave Hsy := Hback $$ Hwg [Hwss]
  · iunfold mvcc.ownWatcherSet; iexact Hwss
  icases mvcc.ownWatcherGroup_watchers (mvcc.syncedAddr s) σ.Ws $$ Hsy with ⟨%v2, Hwg, -, -⟩
  (try wp_auto)
  wp_apply hNew as %gv Hgv
  (try wp_auto)
  ihave Hsy := Hgv $$ %(mvcc.syncedAddr s) Hwg
  -- the lock's new state
  imod ghostVar_update (σ.restoreSt L') γ.wst σ $$ Hσ with Hσ
  ihave HwlL : monoListAuthOwn γ.wlog (1 : Qp).half L $$ [HwlL]
  · rw [HLL]; iexact HwlL
  imod mvcc.wlog_update_halves γ L L' hLR $$ HwlW HwlL with ⟨HwlW, HwlL⟩
  imod mono_nat_own_update L'.length hLL' $$ Hrel with ⟨Hrel, -⟩
  ihave Hmem' : [∗map] w ↦ x ∈ (σ.restoreSt L').ST, mvcc.memberRes γ 1 (σ.restoreSt L') w x $$ [Hmem]
  · rw [show (σ.restoreSt L').ST = mvcc.gmapMapK (fun w st => if (σ.Ws !! w).isSome then
        mvcc.setRestore st else st) σ.ST from rfl]
    iapply (mvcc.bigSepM_gmapMapK _ _ _).2
    iapply (BigSepM.bigSepM_impl (m := σ.ST)) $$ Hmem
    iintro !> %k %x %hk H
    iapply mvcc.memberRes_restoreSt γ σ Hset L' k x hk
    iframe H Hcert
  have e1 : (σ.restoreSt L').Lmu = L' := rfl
  have e2 : (σ.restoreSt L').Ws = ∅ := rfl
  have e3 : (σ.restoreSt L').Wu = σ.Wu ∪ σ.Ws := rfl
  have e4 : (σ.restoreSt L').Wo = σ.Wo := rfl
  have e5 : (σ.restoreSt L').M = σ.M := rfl
  have e6 : (σ.restoreSt L').vs = σ.vs := rfl
  have e7 : (σ.restoreSt L').vbs = σ.vbs := rfl
  have e8 : (σ.restoreSt L').VB = σ.VB := rfl
  have eo : ∀ w x, mvcc.outRes (GF := GF) γ (σ.restoreSt L') w x = mvcc.outRes γ σ w x :=
    fun _ _ => rfl
  ihave HPf : mvcc.watchStoreBody s γ 1 (σ.restoreSt L') $$ [Hσ HwlL HlogQ Hsy Hun Hvf Hvs Hvcap Hvbs
      Hst Hwo Hmeta Hwt Hmem']
  · iunfold mvcc.watchStoreBody
    simp only [named, e1, e2, e3, e4, e5, e6, e7, e8, eo]
    iframe Hσ Hsy Hun Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmfix Hmem' HcL'
    isplitl [HwlL HlogQ]
    · iunfold mvcc.wlogQ; iunfold mvcc.logQ at HlogQ; iframe HwlL HlogQ
    isplitr
    · ipureintro; exact Hvlen
    isplitr
    · iapply (BigSepM.bigSepM_mono (fun {k x} _ => by exact .rfl)) $$ Hout
    ipureintro; exact Hok.restoreSt L'
  ihave Hwsf : mvcc.wsFields s γ 1 $$ [Hfs Hwsd]
  · iunfold mvcc.wsFields; iexists st; iframe Hstp Hfs; iunfold mvcc.wsDep at Hwsd; iexact Hwsd
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl HPf Hrel Hwsf]
  · inext; iunfold mvcc.watchStoreInv; iexists (σ.restoreSt L'); rw [e1]; iframe HPf Hrel Hwsf; ipureintro
    exact ⟨mvcc.WsState.restoreSt_settled Hset L' hLL', mvcc.WsState.restoreSt_srBelow Hsrb L' hLL',
      mvcc.WsState.restoreSt_unsRst Hurst L' hLL'⟩
  (try wp_auto)
  iapply HΦ
  iexists p'
  iframe Hcl Hfrag Hown HhP Hold Hnew'
  isplitr
  · ipureintro; exact ⟨hbk', hkb'⟩
  iunfold mvcc.watchWriter
  simp only [mvcc.wBudget]
  iframe HcL' Htoks HwlW

end proof

end EtcdGrove
end Perennial
