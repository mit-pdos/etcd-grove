/-
Proof of `Spec/.../mvcc/watcher__send.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcher__send
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Verify

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

/-- Two metas of a watcher agree. -/
theorem watcherMeta_agree (γ : WsNames) (w : Loc) (γw γw' : WatcherNames) :
    ⊢ watcherMeta (GF := GF) γ w γw -∗ watcherMeta γ w γw' -∗ ⌜γw = γw'⌝ := by
  unfold watcherMeta
  iintro H1 H2
  iapply ghostMapElem_agree $$ H1 H2

/-- A live watcher's entry is not in a closed channel. -/
theorem chanWatcher_closed_live (γ : WsNames) (γc : WatchChanNames) (sent : List RespM) (w : Loc)
    (γw : WatcherNames) (ql : Qp) :
    ⊢ watcherMeta (GF := GF) γ w γw -∗ dghostVar γw.live (DFrac.own ql) true -∗
      chanWatcher γ γc true sent w -∗ False := by
  iintro #Hm Hl Hc
  iunfold chanWatcher at Hc
  icases Hc with ⟨%γw', %r', %fcs', %evsw', %D, %d', #Hm', %Hwc, #Hf', Ha, %HD, #HDf, #Hwf, Hlc⟩
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
  icases Hc with ⟨%γw', %r', %fcs', %evsw', %D, %d', #Hm', %Hwc, #Hf', Ha, %HD, #HDf, #Hwf, Hlc⟩
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
    · ipureintro
      refine ⟨by simp [HD1], ?_⟩
      rw [hfilt, hDf]
      simp [Deliv.sent, hre, HD2]
    iintro !>
    iapply BigSepL.bigSepL_snoc.2
    iframe HDf
    iexists fs
    iframe Hfi
    ipureintro; rfl
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
    · ipureintro
      refine ⟨by simp [HD1], ?_⟩
      rw [hfilt, hDf, List.map_append, HD2, List.map_append]
      congr 1
      split <;> simp [hre]
    iintro !>
    iapply BigSepL.bigSepL_snoc.2
    iframe HDf
    iexists fs
    iframe Hfi
    ipureintro; exact hk

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

namespace mvcc
/-- The (pointer, event) pairs of the first `m` events the filters keep. -/
def keptPairs (fs : List (EvM → Bool)) (es : List Loc) (evm : List EvM) (m : Nat) : List (Loc × EvM) :=
  ((es.zip evm).take m).filter (fun x => fs.all (fun p => !p x.2))
theorem keptPairs_succ (fs : List (EvM → Bool)) (es : List Loc) (evm : List EvM) (m : Nat)
    (e : Loc) (ev : EvM) (he : es[m]? = some e) (hev : evm[m]? = some ev) :
    keptPairs fs es evm (m + 1) =
      keptPairs fs es evm m ++ (if fs.all (fun p => !p ev) then [(e, ev)] else []) := by
  unfold keptPairs
  have hz : (es.zip evm)[m]? = some (e, ev) := by
    rw [List.getElem?_zip_eq_some]; exact ⟨he, hev⟩
  rw [List.take_add_one, hz]
  simp only [Option.toList_some, List.filter_append, List.filter_cons, List.filter_nil]
  try (split <;> simp_all)

theorem evIs_filter (p : Loc × EvM → Bool) (l : List (Loc × EvM)) :
    ([∗list] x ∈ l, evIs (GF := GF) x.1 x.2) ⊢ [∗list] x ∈ l.filter p, evIs x.1 x.2 := by
  refine intuitionistic_alias.trans ?_
  apply BigSepL.bigSepL_intro
  intro k x hx
  have hm : x ∈ l := (List.mem_filter.1 (List.mem_of_getElem? hx)).1
  exact intuitionistically_elim.trans (BigSepL.bigSepL_mem hm)

theorem keptPairs_all (fs : List (EvM → Bool)) (es : List Loc) (evm : List EvM) (m : Nat)
    (hl : es.length = evm.length) (hm : es.length ≤ m) :
    keptPairs fs es evm m = (es.zip evm).filter (fun x => fs.all (fun p => !p x.2)) := by
  unfold keptPairs
  rw [List.take_of_length_le (by simp [hl] at *; omega)]

theorem keptPairs_snd (fs : List (EvM → Bool)) (es : List Loc) (evm : List EvM)
    (hl : es.length = evm.length) :
    ((es.zip evm).filter (fun x => fs.all (fun p => !p x.2))).map Prod.snd = filtered fs evm := by
  unfold filtered
  induction es generalizing evm with
  | nil => cases evm <;> simp_all
  | cons e es ih =>
    cases evm with
    | nil => simp at hl
    | cons ev evm =>
      simp only [List.zip_cons_cons, List.filter_cons]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      split <;> simp_all

end mvcc

theorem mvcc.watcher.send.wp_proof (hVerify : verify.Verify.spec (GF := GF) (hG := hG)) :
    mvcc.watcher.send.spec (GF := GF) (hG := hG) := by
  intro γ w γw r fcs ch qc ql evsw d wr es evm dq
  wp_start as ⟨#Hmeta, #Hfix, #Hfok, #Hwch, Hch, Hlive, Hevs, Hsl, #Hes, %Hpure⟩
  obtain ⟨Hlen, Hcomp, Hid, Hrevle, Hstart⟩ := Hpure
  ihave #Hfix' := Hfix
  iunfold mvcc.watcherFixed at Hfix'
  icases Hfix' with ⟨%Hwnn, %ks, %ens, #Hkey, #Hks, #Hend, #Hens, #HstartRev, #Hidf, #Hfcs⟩
  ihave #Hfok' := Hfok
  iunfold mvcc.filtersOk at Hfok'
  icases Hfok' with ⟨%fs, #Hfi⟩
  ihave #Hfi' := Hfi
  iunfold mvcc.filtersImpl at Hfi'
  icases Hfi' with ⟨%fps, #Hfps, %Hfpl, #Hfsp⟩
  ihave %Hfcsl := ownSlice_len $$ Hfps
  ihave %Hesl := ownSlice_len $$ Hsl
  wp_auto
  wp_join iprop(∃ (evs2 : GoSlice) (es2 : List Loc) (dq2 : DFrac),
      "w" ∷ w_ptr ↦ w ∗
      "wr" ∷ wr_ptr ↦ { wr with Events' := evs2 } ∗ "Hsl2" ∷ evs2 ↦*{dq2} es2 ∗
      "#Hes2" ∷ ([∗list] x ∈ es2.zip (mvcc.filtered fs evm), mvcc.evIs x.1 x.2) ∗
      "%Hl2" ∷ ⌜es2.length = (mvcc.filtered fs evm).length⌝ ∗
      "Hback" ∷ ((evs2 ↦*{dq2} es2 -∗ wr.Events' ↦*{dq} es) ∧
        (evs2 ↦*□ es2 -∗ |==> wr.Events' ↦*□ es))) with [w wr Hsl]
    as ⟨%evs2, %es2, %dq2, w, wr, Hsl2, #Hes2, %Hl2, Hback⟩
  · have hfps : fps = [] := by
      have h0 : fcs.len = W64 0 := by simpa using Hif
      apply List.eq_nil_of_length_eq_zero; rw [Hfcsl.1, h0]; rfl
    have hfs : fs = [] := List.eq_nil_of_length_eq_zero (by rw [← Hfpl, hfps]; rfl)
    have hfe : mvcc.filtered fs evm = evm := by
      subst hfs; unfold mvcc.filtered; simp
    iexists wr.Events', es, dq
    rw [hfe]
    iframe Hsl Hes w
    isplitl [wr]
    · iexact wr
    isplitr
    · ipureintro; exact Hlen
    isplit
    · iintro H; iexact H
    · iintro H; imodintro; iexact H
  · wp_apply (wp_slice_make3 (V := Loc) (W64 0) wr.Events'.len (by constructor <;> word))
      as %ne0 ⟨Hne0, Hcap0, -⟩
    rename_i igo
    irename : (igo ↦ zero_val w64 : IProp GF) => Higo
    ihave IH : iprop(∃ (n k : w64) (nev : GoSlice),
        "i" ∷ i_ptr ↦ n ∗ "Higo" ∷ igo ↦ k ∗ "ne" ∷ ne_ptr ↦ nev ∗
        "Hne" ∷ nev ↦* ((mvcc.keptPairs fs es evm (sint.nat n)).map Prod.fst) ∗
        "Hcap" ∷ ownSliceCap Loc nev (DFrac.own 1) ∗
        "w" ∷ w_ptr ↦ w ∗ "wr" ∷ wr_ptr ↦ wr ∗ "Hsl" ∷ wr.Events' ↦*{dq} es ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z wr.Events'.len⌝) $$ [i Higo ne Hne0 Hcap0 w wr Hsl]
    · iexists W64 0, _, ne0
      simp only [named]
      have h0 : mvcc.keptPairs fs es evm (sint.nat (W64 0)) = [] := by
        unfold mvcc.keptPairs; rw [show sint.nat (W64 0) = 0 from rfl]; simp
      rw [h0]
      iframe
      ipureintro; exact ⟨by decide, Hesl.2⟩
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat n < es.length := by have := Hesl.1; word
      obtain ⟨en, Hen⟩ : ∃ en, es[sint.nat n]? = some en := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨evn, Hevn⟩ : ∃ evn, evm[sint.nat n]? = some evn :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
      rw [ite_eq_left (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z wr.Events'.len by constructor <;> word)]
      wp_apply wp_load_slice_index wr.Events' (sint.Z n) es _ en Hn.1 $$ [Hsl] as Hsl
      · iframe Hsl; ipureintro; exact Hen
      have hzip : (es.zip evm)[sint.nat n]? = some (en, evn) := by
        rw [List.getElem?_zip_eq_some]; exact ⟨Hen, Hevn⟩
      ihave #He : mvcc.evIs en evn $$ []
      · iapply (BigSepL.bigSepL_lookup hzip) $$ Hes
      wp_join iprop(∃ (b : Bool), "filtered" ∷ filtered_ptr ↦ b ∗ "Hsl" ∷ wr.Events' ↦*{dq} es ∗
          "wr" ∷ wr_ptr ↦ wr ∗ "Higo" ∷ igo ↦ n ∗
          "%Hb" ∷ ⌜b = !(fs.all (fun p => !p evn))⌝) at next with [filtered filter i Hsl wr Higo]
        as ⟨%b, filtered, Hsl, wr, Higo, %Hb⟩
      · ihave IH2 : iprop(∃ (j : w64) (fv : GoFunc), "i" ∷ i_ptr ↦ j ∗ "filter" ∷ filter_ptr ↦ fv ∗
            "filtered" ∷ filtered_ptr ↦ false ∗ "Hsl" ∷ wr.Events' ↦*{dq} es ∗
            "wr" ∷ wr_ptr ↦ wr ∗ "Higo" ∷ igo ↦ n ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z fcs.len ∧
              (fs.take (sint.nat j)).all (fun p => !p evn) = true⌝) $$ [filtered filter i Hsl wr Higo]
        · iexists W64 0, _
          simp only [named]
          iframe
          ipureintro; refine ⟨by decide, Hfcsl.2, ?_⟩
          rw [show sint.nat (W64 0) = 0 from rfl]; rfl
        wp_for IH2
        wp_if_destruct
        · have Hjl : sint.nat j < fps.length := by have := Hfcsl.1; word
          obtain ⟨fv, Hfv⟩ : ∃ fv, fps[sint.nat j]? = some fv := ⟨_, List.getElem?_eq_getElem Hjl⟩
          obtain ⟨p, Hp⟩ : ∃ p, fs[sint.nat j]? = some p :=
            ⟨_, List.getElem?_eq_getElem (by rw [← Hfpl]; exact Hjl)⟩
          rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z fcs.len by constructor <;> word)]
          wp_apply wp_load_slice_index fcs (sint.Z j) fps DFrac.discard fv Hj.1 $$ [] as -
          · iframe Hfps; ipureintro; exact Hfv
          rw [ite_eq_left (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z wr.Events'.len by constructor <;> word)]
          wp_apply wp_load_slice_index wr.Events' (sint.Z n) es _ en Hn.1 $$ [Hsl] as Hsl
          · iframe Hsl; ipureintro; exact Hen
          have hfz : (fps.zip fs)[sint.nat j]? = some (fv, p) := by
            rw [List.getElem?_zip_eq_some]; exact ⟨Hfv, Hp⟩
          ihave #Hf : mvcc.filterSpec fv p $$ []
          · iapply (BigSepL.bigSepL_lookup hfz) $$ Hfsp
          iunfold mvcc.filterSpec at Hf
          wp_apply Hf $$ [] as %bf %Hbf
          · iexact He
          wp_if_destruct
          · have hpe : p evn = false := by simp_all
            try wp_auto
            wp_for_post
            iframe
            iexists j + W64 1, fv
            simp only [named]
            iframe
            ipureintro
            refine ⟨by word, by word, ?_⟩
            rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hp]
            simp [Hj.2.2, hpe]
          · have hpe : p evn = true := by simp_all
            try wp_auto
            wp_for_post
            isplitr
            · ipureintro; rfl
            iexists true
            iframe
            ipureintro
            have hall : (fs.all fun p => !p evn) = false :=
              List.all_eq_false.2 ⟨p, List.mem_of_getElem? Hp, by simp [hpe]⟩
            rw [hall]; rfl
        · isplitr
          · itrivial
          iexists false
          iframe
          ipureintro
          have htk : fs.take (sint.nat j) = fs := List.take_of_length_le (by
            rw [← Hfpl, Hfcsl.1]; word)
          rw [htk] at Hj
          rw [Hj.2.2]; rfl
      subst Hb
      by_cases hk : (fs.all fun p => !p evn) = true
      · rw [hk]
        wp_auto
        rw [ite_eq_left (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z wr.Events'.len by constructor <;> word)]
        wp_apply wp_load_slice_index wr.Events' (sint.Z n) es _ en Hn.1 $$ [Hsl] as Hsl
        · iframe Hsl; ipureintro; exact Hen
        wp_apply wp_slice_literal (l := [en])
        isplitr
        · ipureintro; rfl
        iintro %lit ⟨Hlit, -⟩
        wp_auto
        wp_apply wp_slice_append $$ [$Hne $Hcap $Hlit] as %s' ⟨Hne, Hcap, -⟩
        try wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, n, s'
        simp only [named]
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word,
          mvcc.keptPairs_succ fs es evm _ en evn Hen Hevn, hk]
        simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil]
        iframe
        ipureintro; constructor <;> word
      · have hk' : (fs.all fun p => !p evn) = false := by simpa using hk
        rw [hk']
        try wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, n, nev
        simp only [named]
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word,
          mvcc.keptPairs_succ fs es evm _ en evn Hen Hevn, hk']
        simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
        iframe
        ipureintro; constructor <;> word
    · have hnl : es.length ≤ sint.nat n := by have := Hesl.1; word
      rw [mvcc.keptPairs_all fs es evm _ Hlen hnl]
      isplitr
      · itrivial
      iexists nev, ((es.zip evm).filter (fun x => fs.all (fun p => !p x.2))).map Prod.fst,
        DFrac.own 1
      simp only [named]
      iframe w wr Hne
      have hz : (((es.zip evm).filter (fun x => fs.all (fun p => !p x.2))).map Prod.fst).zip
          (mvcc.filtered fs evm) = (es.zip evm).filter (fun x => fs.all (fun p => !p x.2)) := by
        rw [← mvcc.keptPairs_snd fs es evm Hlen, ← List.unzip_fst, ← List.unzip_snd, List.zip_unzip]
      rw [hz]
      isplitr
      · iapply mvcc.evIs_filter $$ Hes
      isplitr
      · ipureintro
        rw [← mvcc.keptPairs_snd fs es evm Hlen, List.length_map, List.length_map]
      isplit
      · iintro -; iexact Hsl
      · iintro -
        imod ownSlice_persist $$ Hsl with #Hsl
        imodintro
        iexact Hsl
  wp_apply (hVerify _ _ iprop(w_ptr ↦ w ∗ wr_ptr ↦ { wr with Events' := evs2 } ∗
      evs2 ↦*{dq2} es2)) $$ [w wr Hsl2] as ⟨w, wr, Hsl2⟩
  · iframe w wr Hsl2
    iintro ⟨w, wr, Hsl2⟩
    ihave %Hsl2l := ownSlice_len $$ Hsl2
    wp_auto
    wp_if_destruct
    · have Hsp : 0 < sint.Z r.startRev := by simpa using Hif
      ihave IH : iprop(∃ (n : w64) (evv : Loc), "i" ∷ i_ptr ↦ n ∗ "ev" ∷ ev_ptr ↦ evv ∗
          "w" ∷ w_ptr ↦ w ∗ "wr" ∷ wr_ptr ↦ { wr with Events' := evs2 } ∗
          "Hsl2" ∷ evs2 ↦*{dq2} es2 ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z evs2.len⌝) $$ [i ev w wr Hsl2]
      · iexists W64 0, _
        simp only [named]
        iframe
        ipureintro; exact ⟨by decide, Hsl2l.2⟩
      wp_for IH
      wp_if_destruct
      · have Hlt : sint.nat n < es2.length := by have := Hsl2l.1; word
        obtain ⟨en, Hen⟩ : ∃ en, es2[sint.nat n]? = some en := ⟨_, List.getElem?_eq_getElem Hlt⟩
        obtain ⟨evn, Hevn⟩ : ∃ evn, (mvcc.filtered fs evm)[sint.nat n]? = some evn :=
          ⟨_, List.getElem?_eq_getElem (by rw [← Hl2]; exact Hlt)⟩
        rw [ite_eq_left (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z evs2.len by constructor <;> word)]
        wp_apply wp_load_slice_index evs2 (sint.Z n) es2 _ en Hn.1 $$ [Hsl2] as Hsl2
        · iframe Hsl2; ipureintro; exact Hen
        have hzip : (es2.zip (mvcc.filtered fs evm))[sint.nat n]? = some (en, evn) := by
          rw [List.getElem?_zip_eq_some]; exact ⟨Hen, Hevn⟩
        ihave #He : mvcc.evIs en evn $$ []
        · iapply (BigSepL.bigSepL_lookup hzip) $$ Hes2
        icases mvcc.evIs_modRev en evn $$ He with ⟨%p, #HK, #HM⟩
        have hge := Hstart Hsp evn (mvcc.mem_filtered (List.mem_of_getElem? Hevn))
        wp_auto
        rw [_root_.decide_eq_false (show ¬ sint.Z evn.kv.modRev < sint.Z r.startRev by omega)]
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, en
        simp only [named]
        iframe
        ipureintro; constructor <;> word
      · iexists _
        iframe
        ipureintro; rfl
    · iexists _
      iframe w wr Hsl2
      ipureintro; rfl
  ihave %Hsl2l := ownSlice_len $$ Hsl2
  have hev0 : (wr.Events'.len = W64 0) ↔ evm = [] := by
    constructor
    · intro h; apply List.eq_nil_of_length_eq_zero; rw [← Hlen, Hesl.1, h]; rfl
    · intro h; rw [h] at Hlen; have := Hesl.1; rw [Hlen] at this; simp at this; word
  ihave #Hwch' := Hwch
  iunfold mvcc.watcherChan at Hwch'
  icases Hwch' with ⟨#Hisch, #Hinv, #Hregw⟩
  by_cases hA : evm ≠ [] ∧ mvcc.filtered fs evm = []
  · -- every event filtered out: delivered, nothing sent
    have h1 : decide (wr.Events'.len = W64 0) = false := decide_eq_false (fun h => hA.1 (hev0.1 h))
    have h2 : evs2.len = W64 0 := by
      have : es2.length = 0 := by rw [Hl2, hA.2]; rfl
      have h3 := Hsl2l.1; rw [this] at h3; word
    rw [h1]
    iapply wp_fupd
    wp_auto_lc 1
    rw [h2]
    wp_auto
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
    iunfold mvcc.watchChanInv at Hi
    iNamed Hi
    ihave %Hwl := mvcc.reg_mem _ _ _ $$ Hreg Hregw
    have hds : Deliv.sent (evm, mvcc.filtered fs evm) = false := by
      simp [Deliv.sent, hA.1, hA.2]
    imod mvcc.entries_deliver γ γw.wc (mvcc.chanIsClosed s) sent L w γw r fcs fs evsw d evm
      (mvcc.filtered fs evm) ⟨w, wr.WatchID', mvcc.filtered fs evm, wr.Revision'⟩ Hnd Hwl rfl rfl rfl
      $$ Hmeta Hfix Hfi Hevs Hws with ⟨Hevs, Hws⟩
    have hsent : sent ++ (if Deliv.sent (evm, mvcc.filtered fs evm) then
        [(⟨w, wr.WatchID', mvcc.filtered fs evm, wr.Revision'⟩ : mvcc.RespM)] else []) = sent := by
      rw [hds]; simp
    irevert Hws; rw [hsent]; iintro Hws
    imod Hclose $$ [Hch Hrecv Hregl Hcl Hreg Hws] with -
    · inext
      iunfold mvcc.watchChanInv
      iexists s, sent, recv, vs, L
      simp only [named]
      iframe
      iframe #
      ipureintro; exact ⟨Hpre, Hinfl, Hnd⟩
    icases Hback with ⟨-, Hb⟩
    imod ownSlice_persist $$ Hsl2 with #Hsl2
    imod Hb $$ Hsl2 with #Hsl
    imodintro
    iapply HΦ
    simp only [↓reduceIte, hA.1]
    iframe Hch Hlive Hsl Hevs
  · -- the send
    have hsend : Deliv.sent (evm, mvcc.filtered fs evm) = true := by
      by_cases he : evm = []
      · simp [Deliv.sent, he]
      · have : mvcc.filtered fs evm ≠ [] := fun h => hA ⟨he, h⟩
        simp [Deliv.sent, List.isEmpty_iff, this]
    by_cases he : evm = []
    rw [decide_eq_true (hev0.2 he)]
    wp_auto
    rotate_left
    rw [decide_eq_false (fun h => he (hev0.1 h))]
    wp_auto
    have hne : mvcc.filtered fs evm ≠ [] := fun h => hA ⟨he, h⟩
    have hz : evs2.len ≠ W64 0 := by
      intro h0; apply hne; apply List.eq_nil_of_length_eq_zero; rw [← Hl2, Hsl2l.1, h0]; rfl
    rw [decide_eq_false hz]
    wp_auto
    all_goals
      wp_bind (App (Val (GoInstruction SelectStmt)) _)
      iapply chan.wp_select_nonblocking
      isplit
      · iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.nonblockingClausePre]
          iexists WatchResponse, inferInstance, inferInstance, inferInstance, inferInstance, ch,
            γw.wc.ch, { wr with Events' := evs2 }
          isplit
          · ipureintro; exact ⟨rfl, rfl⟩
          isplit
          · iexact Hisch
          unfold nonblockingSendAu
          isplit
          · unfold nonblockingSendAuInner
            iinv Hinv with Hi Hclose
            all_goals try exact CoPset.subseteq_top
            iapply fupd_mask_intro Std.LawfulSet.empty_subset
            iintro Hmask
            inext
            iunfold mvcc.watchChanInv at Hi
            iNamed Hi
            ihave %Hwl := mvcc.reg_mem _ _ _ $$ Hreg Hregw
            iexists s
            iframe Hch
            have hpre := Hpre.length_le
            rcases s with (_ | ⟨b0, bs⟩) | _ | _ | _ | _ | _ | (_ | ⟨b0, bs⟩)
            all_goals dsimp only
            all_goals first | itrivial | skip
            case Closed.nil | Closed.cons =>
              irevert Hws; simp only [mvcc.chanIsClosed]; iintro Hws
              ihave Hw := (BigSepL.bigSepL_mem (Φ := fun x => mvcc.chanWatcher γ γw.wc true sent x)
                Hwl) $$ Hws
              iapply mvcc.chanWatcher_closed_live γ γw.wc sent w γw ql $$ Hmeta Hlive Hw
            all_goals
              iintro Hchan
              imod ownSlice_persist $$ Hsl2 with #Hsl2p
              ihave #Hresp : mvcc.respIs { wr with Events' := evs2 }
                  ⟨w, wr.WatchID', mvcc.filtered fs evm, wr.Revision'⟩ $$ []
              · iunfold mvcc.respIs
                isplitr
                · ipureintro; exact ⟨rfl, rfl, Hcomp⟩
                iexists es2
                iframe Hsl2p Hes2
                ipureintro; exact Hl2
              ihave #Hrok : mvcc.respOk (⟨w, wr.WatchID', mvcc.filtered fs evm, wr.Revision'⟩ : mvcc.RespM)
                  $$ []
              · iunfold mvcc.respOk
                isplitr
                · ipureintro; intro ev hev; exact Hrevle ev (mvcc.mem_filtered hev)
                iexists r, fcs
                iframe Hfix
                ipureintro
                intro hne
                exact Hid (fun h => hne (by rw [h]; rfl))
              imod mvcc.entries_deliver γ γw.wc _ sent L w γw r fcs fs evsw d evm
                (mvcc.filtered fs evm) ⟨w, wr.WatchID', mvcc.filtered fs evm, wr.Revision'⟩ Hnd Hwl
                rfl rfl rfl $$ Hmeta Hfix Hfi Hevs Hws with ⟨Hevs, Hws⟩
              have hs2 : sent ++ (if Deliv.sent (evm, mvcc.filtered fs evm) then
                  [(⟨w, wr.WatchID', mvcc.filtered fs evm, wr.Revision'⟩ : mvcc.RespM)] else []) =
                  sent ++ [⟨w, wr.WatchID', mvcc.filtered fs evm, wr.Revision'⟩] := by
                rw [hsend]; rfl
              irevert Hws; rw [hs2]; iintro Hws
              ihave #Hvs' := mvcc.respsIs_snoc vs sent recv.length hpre _ _ $$ [$Hvs $Hresp]
              icases Hback with ⟨-, Hb⟩
              imod Hb $$ Hsl2p with #Hsl
              imod Hmask with -
              imod Hclose $$ [Hchan Hrecv Hregl Hcl Hreg Hws] with -
              · inext
                iunfold mvcc.watchChanInv
                iexists _, sent ++ [⟨w, wr.WatchID', mvcc.filtered fs evm, wr.Revision'⟩], recv,
                  vs ++ [{ wr with Events' := evs2 }], L
                simp only [named]
                isplitl [Hchan]
                · iexact Hchan
                isplitl [Hrecv]
                · iexact Hrecv
                isplitr
                · ipureintro; exact Hpre.trans (List.prefix_append _ _)
                isplitr
                · ipureintro; simp_all [mvcc.chanInflight]
                isplitr
                · iexact Hvs'
                isplitr
                · iintro !>
                  iapply BigSepL.bigSepL_snoc.2
                  iframe Hok Hrok
                isplitl [Hregl]
                · iexact Hregl
                isplitl [Hcl]
                · iapply mvcc.closedFlag_congr (by simp [mvcc.chanIsClosed]) $$ Hcl
                isplitl [Hreg]
                · iexact Hreg
                isplitr
                · ipureintro; exact Hnd
                iapply mvcc.chanWatchers_congr γ γw.wc (by simp [mvcc.chanIsClosed]) $$ Hws
              imodintro
              wp_auto
              iapply HΦ
              simp only [↓reduceIte]
              iframe Hch Hlive Hsl Hevs
          · itrivial
        · iapply BigAndL.bigAndL_nil.2
          itrivial
      · wp_auto
        icases Hback with ⟨Hb, -⟩
        ihave Hsl := Hb $$ Hsl2
        ihave Hevs := mvcc.evs_drop evm _ _ $$ Hevs
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe Hch Hlive Hsl Hevs

end proof

end EtcdGrove
end Perennial
