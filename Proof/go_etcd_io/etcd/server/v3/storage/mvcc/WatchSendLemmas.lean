/-
**The watcher channel's send lemmas** (moved out of `watcher__send.lean`, 2026-11-01, for
`chooseAll`'s compaction response, watches across a compaction): a watcher's registration
(`reg_mem`), a live watcher's channel is open (`chanWatcher_closed_live`), a delivery recorded
(`chanWatcher_deliver`, `entries_deliver`), the sent values (`respsIs_snoc`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

namespace mvcc

/-- The half authorities of a monotone list, combined and appended to. -/
theorem monoList_halves_app {A : Type} [Pos.Countable A] (γl : GName) (l1 l2 ext : List A) :
    ⊢ monoListAuthOwn (GF := GF) γl (1 : Qp).half l1 -∗ monoListAuthOwn γl (1 : Qp).half l2 ==∗
      ⌜l1 = l2⌝ ∗ monoListAuthOwn γl (1 : Qp).half (l1 ++ ext) ∗
        monoListAuthOwn γl (1 : Qp).half (l1 ++ ext) := by
  have hh := fun (l : List A) =>
    (monoListAuthOwn_fractional (GF := GF) γl l).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hh
  iintro H1 H2
  ihave %Hag := monoListAuthOwn_agree γl _ _ l1 l2 $$ H1 H2
  obtain ⟨-, rfl⟩ := Hag
  ihave H : monoListAuthOwn γl 1 l1 $$ [H1 H2]
  · iapply (hh l1).2; iframe H1 H2
  imod monoListAuthOwn_update_app ext $$ H with ⟨H, -⟩
  icases (hh (l1 ++ ext)).1 $$ H with ⟨H1, H2⟩
  imodintro
  iframe H1 H2
  ipureintro; rfl

/-- A watcher's registration: it is in the channel's list. -/
theorem reg_mem (γc : WatchChanNames) (L : List Loc) (w : Loc) :
    ⊢ ghostMapAuth (GF := GF) γc.reg 1 (regMap L) -∗ ghostMapElem γc.reg w DFrac.discard () -∗
      ⌜w ∈ L⌝ := by
  iintro Ha He
  ihave %H := ghost_map_lookup $$ Ha He
  ipureintro
  exact (regMap_lookup L w).1 (by rw [show regMap L !! w = (regMap L).lookup w from rfl, H]; rfl)

-- `watcherMeta_agree`: `InvWatchStore.lean` (unit W-M2).

/-- A live watcher's entry is not in a closed channel. -/
theorem chanWatcher_closed_live (γ : WsNames) (γc : WatchChanNames) (sent : List RespM) (w : Loc)
    (γw : WatcherNames) (ql : Qp) :
    ⊢ watcherMeta (GF := GF) γ w γw -∗ dghostVar γw.live (DFrac.own ql) true -∗
      chanWatcher γ γc true sent w -∗ False := by
  iintro #Hm Hl Hc
  iunfold chanWatcher at Hc
  icases Hc with ⟨%γw', %r', %fcs', %evsw', %D, %d', #Hm', %Hwc, %Hslo, #Hf', Ha, %HD, #HDf, #Hwf, Hlc⟩
  ihave %He := watcherMeta_agree γ w γw γw' $$ Hm Hm'
  subst He
  icases Hlc with (⟨%Hf, -⟩ | Hcan)
  · cases Hf
  · iunfold cancelled at Hcan
    ihave %Hag := dghostVar_agree $$ Hl Hcan
    cases Hag

/-- Another watcher's entry, with responses for `w` appended. -/
theorem chanWatcher_other (γ : WsNames) (γc : WatchChanNames) (closed : Bool) (sent ext : List RespM)
    (w x : Loc) (hx : x ≠ w) (hext : ∀ y ∈ ext, y.w = w) :
    chanWatcher (GF := GF) γ γc closed sent x ⊢ chanWatcher γ γc closed (sent ++ ext) x := by
  have hf : (sent ++ ext).filter (fun y => decide (y.w = x)) = sent.filter (fun y => decide (y.w = x)) := by
    rw [List.filter_append]
    have : ext.filter (fun y => decide (y.w = x)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro y hy; rw [hext y hy]; simpa using Ne.symm hx
    rw [this, List.append_nil]
  unfold chanWatcher
  rw [hf]

/-- The deliveries' prefixes still end at revisions after one more delivery, given the new
events' bound. -/
theorem delivsCut_snoc (γ : WsNames) (r : WatchRange) (lo : Nat) (D : List Deliv) (dl : Deliv)
    (evs : List EvM) (d : Nat) (h : ((D ++ [dl]).map Prod.fst).flatten = evs) :
    delivsCut (GF := GF) γ r lo D ∗ evsWf γ r lo evs d ⊢ delivsCut γ r lo (D ++ [dl]) := by
  iintro ⟨#Hc, #Hwf⟩
  iunfold delivsCut at Hc
  iunfold delivsCut
  iintro !> %k %hk
  by_cases hk' : k ≤ D.length
  · rw [List.take_append_of_le_length hk']
    iapply Hc $$ %k %hk'
  · have hk2 : (D ++ [dl]).length ≤ k := by simp at hk ⊢; omega
    rw [List.take_of_length_le hk2, h]
    iexists d
    iexact Hwf

/-- The delivery of `evm` (kept: `kept`) to `w`'s entry: the events delivered grow, the
response (if sent) is `w`'s. -/
theorem chanWatcher_deliver (γ : WsNames) (γc : WatchChanNames) (closed : Bool)
    (sent : List RespM) (w : Loc) (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice)
    (fs : List (EvM → Bool)) (evsw : List EvM) (d : Nat) (evm kept : List EvM) (rr : RespM)
    (hk : kept = filtered fs evm) (hrw : rr.w = w) (hre : rr.evs = kept) :
    ⊢ watcherMeta (GF := GF) γ w γw -∗ watcherFixed w r fcs -∗ filtersImpl fcs fs -∗
      (if evm = [] then iprop(True) else
        monoListAuthOwn γw.evs (1 : Qp).half evsw ∗ evsWf γ r γw.lo (evsw ++ evm) d) -∗
      chanWatcher γ γc closed sent w ==∗
      (if evm = [] then iprop(True) else monoListAuthOwn γw.evs (1 : Qp).half (evsw ++ evm)) ∗
      chanWatcher γ γc closed (sent ++ (if Deliv.sent (evm, kept) then [rr] else [])) w := by
  iintro #Hm #Hf #Hfi Hevs Hc
  iunfold chanWatcher at Hc
  icases Hc with ⟨%γw', %r', %fcs', %evsw', %D, %d', #Hm', %Hwc, %Hslo, #Hf', Ha, %HD, #HDf, #Hwf, Hlc⟩
  ihave %He := watcherMeta_agree γ w γw γw' $$ Hm Hm'
  subst He
  ihave %Hag := watcherFixed_agree w r r' fcs fcs' $$ [Hf Hf']
  · iframe Hf Hf'
  obtain ⟨rfl, rfl⟩ := Hag
  obtain ⟨HD1, HD2⟩ := HD
  have hfilt : (sent ++ (if Deliv.sent (evm, kept) then [rr] else [])).filter
      (fun x => decide (x.w = w)) = sent.filter (fun x => decide (x.w = w)) ++
        (if Deliv.sent (evm, kept) then [rr] else []) := by
    rw [List.filter_append]; congr 1
    split <;> simp [hrw]
  have hDf : (D ++ [(evm, kept)]).filter Deliv.sent =
      D.filter Deliv.sent ++ (if Deliv.sent (evm, kept) then [(evm, kept)] else []) := by
    rw [List.filter_append]; congr 1
    simp only [List.filter_cons, List.filter_nil]
    try (split <;> simp_all)
  by_cases hevm : evm = []
  · subst hevm
    have hk0 : kept = [] := by rw [hk]; rfl
    subst hk0
    simp only [↓reduceIte]
    imodintro
    isplitr
    · itrivial
    iunfold chanWatcher
    iexists γw, r, fcs, evsw', D ++ [([], [])], d'
    iframe Hm Hf Ha Hwf Hlc
    isplitr
    · ipureintro; exact Hwc
    isplitr
    · ipureintro; exact Hslo
    isplitr
    · ipureintro
      refine ⟨by simp [HD1], ?_⟩
      rw [hfilt, hDf]
      simp [Deliv.sent, hre, HD2]
    icases HDf with ⟨#HDf, #HDc⟩
    iintro !>
    isplitl
    · iapply BigSepL.bigSepL_snoc.2
      iframe HDf
      iexists fs
      iframe Hfi
      ipureintro; rfl
    iapply delivsCut_snoc γ r γw.lo D ([], []) evsw' d' (by simp [HD1]) $$ [$HDc $Hwf]
  · simp only [hevm, ↓reduceIte]
    icases Hevs with ⟨Hmine, #Hwf2⟩
    imod monoList_halves_app γw.evs evsw evsw' evm $$ Hmine Ha with ⟨%Heq, Hmine, Ha⟩
    subst Heq
    imodintro
    iframe Hmine
    iunfold chanWatcher
    iexists γw, r, fcs, evsw ++ evm, D ++ [(evm, kept)], d
    iframe Hm Hf Ha Hwf2 Hlc
    isplitr
    · ipureintro; exact Hwc
    isplitr
    · ipureintro; exact Hslo
    isplitr
    · ipureintro
      refine ⟨by simp [HD1], ?_⟩
      rw [hfilt, hDf, List.map_append, HD2, List.map_append]
      congr 1
      split <;> simp [hre]
    icases HDf with ⟨#HDf, #HDc⟩
    iintro !>
    isplitl
    · iapply BigSepL.bigSepL_snoc.2
      iframe HDf
      iexists fs
      iframe Hfi
      ipureintro; exact hk
    iapply delivsCut_snoc γ r γw.lo D (evm, kept) (evsw ++ evm) d (by simp [HD1]) $$ [$HDc $Hwf2]

/-- An event's key-value's mod revision, read-only. -/
theorem evIs_modRev (e : Loc) (ev : EvM) :
    evIs (GF := GF) e ev ⊢ ∃ p : Loc,
      e.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"Kv"] ↦□ p ∗
      p.[go_etcd_io.etcd.api.v3.mvccpb.KeyValue, go!"ModRevision"] ↦□ ev.kv.modRev := by
  iintro #H
  iunfold evIs at H
  icases H with ⟨%p, %q, %st, %uf, %sc, %Hnn, #Hev, #Hkv, -⟩
  iunfold kvPtrFixed at Hkv
  icases Hkv with ⟨%ks, %vs, %kst, %kuf, %ksc, -, -, #Hk⟩
  icases event_fields _ _ _ $$ Hev with ⟨-, #HevK, -⟩
  icases kv_fields _ _ _ $$ Hk with ⟨-, #HkM⟩
  iexists p
  iframe HevK HkM

theorem mem_filtered {fs : List (EvM → Bool)} {evm : List EvM} {ev : EvM}
    (h : ev ∈ filtered fs evm) : ev ∈ evm := (List.mem_filter.1 h).1

theorem closedFlag_congr {b1 b2 : Bool} (h : b1 = b2) (P : IProp GF) :
    (if b1 = true then P else iprop(True)) ⊢ (if b2 = true then P else iprop(True)) := by
  subst h; exact .rfl

theorem chanWatchers_congr (γ : WsNames) (γc : WatchChanNames) {b1 b2 : Bool} (h : b1 = b2)
    (sent : List RespM) (L : List Loc) :
    ([∗list] x ∈ L, chanWatcher (GF := GF) γ γc b1 sent x) ⊢
      [∗list] x ∈ L, chanWatcher γ γc b2 sent x := by
  subst h; exact .rfl

theorem evs_drop (evm : List EvM) (A B : IProp GF) :
    (if evm = [] then iprop(True) else iprop(A ∗ B)) ⊢ (if evm = [] then iprop(True) else A) := by
  split
  · exact .rfl
  · exact sep_elim_left

theorem nodup_idx_eq {L : List Loc} (h : L.Nodup) {i k : Nat} {x : Loc} (h1 : L[i]? = some x)
    (h2 : L[k]? = some x) : i = k := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h1
  obtain ⟨hk, hk'⟩ := List.getElem?_eq_some_iff.1 h2
  exact (List.Nodup.getElem_inj h).1 hk'.symm

/-- The delivery to `w`'s entry among the registered watchers' (the others unchanged). -/
theorem entries_deliver (γ : WsNames) (γc : WatchChanNames) (closed : Bool)
    (sent : List RespM) (L : List Loc) (w : Loc) (γw : WatcherNames) (r : WatchRange)
    (fcs : GoSlice) (fs : List (EvM → Bool)) (evsw : List EvM) (d : Nat) (evm kept : List EvM)
    (rr : RespM) (hnd : L.Nodup) (hw : w ∈ L)
    (hk : kept = filtered fs evm) (hrw : rr.w = w) (hre : rr.evs = kept) :
    ⊢ watcherMeta (GF := GF) γ w γw -∗ watcherFixed w r fcs -∗ filtersImpl fcs fs -∗
      (if evm = [] then iprop(True) else
        monoListAuthOwn γw.evs (1 : Qp).half evsw ∗ evsWf γ r γw.lo (evsw ++ evm) d) -∗
      ([∗list] x ∈ L, chanWatcher γ γc closed sent x) ==∗
      (if evm = [] then iprop(True) else monoListAuthOwn γw.evs (1 : Qp).half (evsw ++ evm)) ∗
      ([∗list] x ∈ L, chanWatcher γ γc closed
        (sent ++ (if Deliv.sent (evm, kept) then [rr] else [])) x) := by
  iintro #Hm #Hf #Hfi Hevs Hall
  obtain ⟨i, hi⟩ : ∃ i, L[i]? = some w := List.mem_iff_getElem?.1 hw
  icases (BigSepL.bigSepL_lookup_acc_impl (Φ := fun _ x => chanWatcher γ γc closed sent x) hi) $$ Hall with ⟨Hw, Hback⟩
  imod chanWatcher_deliver γ γc closed sent w γw r fcs fs evsw d evm kept rr hk hrw hre
    $$ Hm Hf Hfi Hevs Hw with ⟨Hmine, Hw⟩
  imodintro
  iframe Hmine
  iapply Hback $$ %(fun (_ : Nat) (x : Loc) => chanWatcher γ γc closed
    (sent ++ (if Deliv.sent (evm, kept) then [rr] else [])) x) [] Hw
  iintro !> %k %y %hy %hki Hy
  have hyw : y ≠ w := by
    rintro rfl
    exact hki (nodup_idx_eq hnd hy hi)
  iapply chanWatcher_other γ γc closed sent _ w y hyw (by split <;> simp [hrw]) $$ Hy

/-- One more response sent: in flight after the others. -/
theorem respsIs_snoc (vs : List WatchResponse) (sent : List RespM) (k : Nat)
    (hk : k ≤ sent.length) (v : WatchResponse) (r : RespM) :
    respsIs (GF := GF) vs (sent.drop k) ∗ respIs v r ⊢ respsIs (vs ++ [v]) ((sent ++ [r]).drop k) := by
  rw [List.drop_append_of_le_length hk]
  unfold respsIs
  iintro ⟨⟨%Hlen, #H⟩, #Hv⟩
  isplitr
  · ipureintro; simp [Hlen]
  imodintro
  iintro %i %v' %r' %Hv' %Hr'
  by_cases hi : i < vs.length
  · rw [List.getElem?_append_left hi] at Hv'
    rw [List.getElem?_append_left (Hlen ▸ hi)] at Hr'
    iapply H $$ %i %v' %r' %Hv' %Hr'
  · have hge : vs.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getElem?_append_right hge] at Hv'
    rw [List.getElem?_append_right (Hlen ▸ hge)] at Hr'
    rw [Hlen] at Hv'
    obtain ⟨hi1, rfl⟩ := List.getElem?_eq_some_iff.mp Hv'
    obtain ⟨hi2, rfl⟩ := List.getElem?_eq_some_iff.mp Hr'
    simp only [List.length_singleton, Nat.lt_one_iff] at hi1
    simp only [hi1, List.getElem_singleton]
    iexact Hv

end mvcc

end lemmas

end EtcdGrove
end Perennial
