/-
**mvcc's candidate API's watch laws** (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`),
proved of the watch stream's implementation (`ApiWatchImpl.lean`). Each `<law>_proof` proves
`<law>.law`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- Two filters that agree on the responses with events select the same events. -/
theorem flatten_filter_evs_eq (ms : List RespM) (p q : RespM → Bool)
    (h : ∀ m ∈ ms, m.evs ≠ [] → p m = q m) :
    ((ms.filter p).map RespM.evs).flatten = ((ms.filter q).map RespM.evs).flatten := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    have ih' := ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))
    by_cases he : m.evs = []
    · simp only [List.filter_cons]
      split <;> split <;> simp_all
    · have hpq := h m List.mem_cons_self he
      simp only [List.filter_cons, hpq]
      split <;> simp_all

/-- The events the views of `ms` carried for `id`. -/
theorem recvEvs_view (ms : List RespM) (id : w64) :
    recvEvs (ms.map respView) id =
      ((ms.filter (fun m => decide (m.id = id))).map RespM.evs).flatten := by
  unfold recvEvs
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.map_cons, List.filter_cons, respView]
    split <;> simp_all

/-- **The last element a predicate holds of**: none, or one whose prefix up to it has every one. -/
theorem last_idx {α : Type} (ms : List α) (p : α → Bool) :
    ms.filter p = [] ∨ ∃ (j : Nat) (m : α), ms[j]? = some m ∧ p m = true ∧
      (ms.take (j + 1)).filter p = ms.filter p := by
  induction ms with
  | nil => left; rfl
  | cons x ms ih =>
    rcases ih with h | ⟨j, m, hj, hm, ht⟩
    · by_cases hx : p x = true
      · right
        refine ⟨0, x, rfl, hx, ?_⟩
        simp [List.filter_cons, hx, h]
      · left; simp [List.filter_cons, hx, h]
    · right
      refine ⟨j + 1, m, by simpa using hj, hm, ?_⟩
      rw [List.take_succ_cons]
      simp only [List.filter_cons]
      rw [ht]

/-- Deliveries kept whole are all sent, and their events are their kept events. -/
theorem delivs_whole (D : List Deliv) (h : ∀ dl ∈ D, dl.2 = dl.1) :
    ((D.filter Deliv.sent).map Prod.snd).flatten = (D.map Prod.fst).flatten := by
  induction D with
  | nil => rfl
  | cons dl D ih =>
    have h1 := h dl List.mem_cons_self
    have ih' := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have hs : Deliv.sent dl = true := by
      unfold Deliv.sent; rw [h1]; cases dl.1 <;> simp
    simp [List.filter_cons, hs, ih', h1]

theorem log_notified (σ : MvccState) : σ.log <+: σ.notifiedLog := by
  unfold MvccState.notifiedLog
  cases σ.pending with
  | none => exact List.prefix_refl _
  | some x => exact List.prefix_append _ _

/-- **A watched log is a prefix of the client's notified history**: in the certificate map (whose
logs are its prefixes), or one of `NewStore`'s (comparable with the certified log, at least two
long); never the map's free element (the map's logs are not empty). -/
theorem evLog_notified (γ : MvccImpl) (σ : MvccState) (L : Log) :
    evLog (GF := GF) γ.st L ∗ mvccStateI γ σ ⊢ ⌜L <+: σ.notifiedLog⌝ := by
  iintro ⟨#Hev, Hσ⟩
  iunfold mvccStateI at Hσ
  icases Hσ with ⟨-, -, -, #Hgi, ⟨%M, HM, %HMok⟩, -, -, %Hreach⟩
  iunfold evLog at Hev
  icases Hev with ⟨#Hsl, #Hok⟩
  iunfold certOk at Hok
  icases Hok with (%Hl | #Hel | #Hel)
  · ihave #Hsl' := idxCert_sealed γ.st.idx σ.log $$ Hgi
    ihave %Hc := idxSealed_cmp γ.st.idx L σ.log $$ Hsl Hsl'
    ipureintro
    have h2 := Hreach.1.len_ge
    have hl : L <+: σ.log := by
      rcases Hc with h | h
      · exact h
      · have hle := h.length_le
        have heq : σ.log = L := h.eq_of_length (by omega)
        rw [heq]; exact List.prefix_refl _
    exact hl.trans (log_notified σ)
  · ihave %Hlk := ghost_map_lookup $$ HM Hel
    obtain ⟨-, -, hp⟩ := HMok _ _ Hlk
    ipureintro; exact hp
  · ihave %Hlk := ghost_map_lookup $$ HM Hel
    obtain ⟨hne, -, -⟩ := HMok _ _ Hlk
    exact absurd rfl hne

/-- **Without filters, each delivery's kept events are its events.** -/
theorem deliv_nofilter (fcs : GoSlice) :
    ∀ D : List Deliv, fcs ↦*□ ([] : List GoFunc) ∗
      □ (∀ dl : Deliv, ⌜dl ∈ D⌝ -∗ ∃ fs, filtersImpl (GF := GF) fcs fs ∗ ⌜dl.2 = filtered fs dl.1⌝) ⊢
        ⌜∀ dl ∈ D, dl.2 = dl.1⌝
  | [] => by iintro _; ipureintro; simp
  | dl :: D => by
    iintro ⟨#Hf, #HD⟩
    ihave %HD' := deliv_nofilter fcs D $$ [Hf HD]
    · iframe Hf
      iintro !> %d %hd
      iapply HD $$ %d %(List.mem_cons_of_mem _ hd)
    icases HD $$ %dl %List.mem_cons_self with ⟨%fs, #Hfi, %Hdl⟩
    iunfold filtersImpl at Hfi
    icases Hfi with ⟨%fps, #Hfps, %Hlen, -⟩
    ihave %Heq := ownSlice_agree _ _ _ _ _ $$ Hf Hfps
    ipureintro
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · have : fs = [] := by
        rw [← Heq] at Hlen; exact List.eq_nil_of_length_eq_zero (by simpa using Hlen.symm)
      subst this
      rw [Hdl]; unfold filtered; simp
    · exact HD' d hd

/-- **On a response with events, the view's id and the view's watcher agree**: its id is its
watcher's (`respOk`), which the channel assigned (`chanRegFact`), as the stream assigned the view's
id to the view's watcher. -/
theorem rcv_agree (γs : WsNames) (γo : WsStreamNames) (γc : WatchChanNames) (hids : γo.ids = γc.ids)
    (id : w64) (w0 : Loc) (rg : WatchRange) (fcs0 : GoSlice) (hrg : rg.id = id)
    (pre : List RespM) (m : RespM) :
    idAssigned (GF := GF) γo id w0 ∗ watcherFixed w0 rg fcs0 ∗ rcvFact γs γc pre m ⊢
      ⌜m.evs ≠ [] → decide (m.id = id) = decide (m.w = w0)⌝ := by
  iintro ⟨#Hia, #Hfx0, #Hf⟩
  iunfold rcvFact at Hf
  icases Hf with ⟨#Hok, -, #Hreg, -⟩
  iunfold respOk at Hok
  icases Hok with ⟨-, %rr, %fcs, #Hfx, %Hid⟩
  iunfold chanRegFact at Hreg
  icases Hreg with ⟨%rr', %fcs', #Hfx', #Hca, -⟩
  ihave %Ha1 := watcherFixed_agree m.w rr rr' fcs fcs' $$ [$Hfx $Hfx']
  obtain ⟨rfl, rfl⟩ := Ha1
  by_cases he : m.evs = []
  · ipureintro; intro h; exact absurd he h
  have hmid : m.id = rr.id := (Hid.1 he)
  by_cases hw : m.w = w0
  · isimp only [hw] at Hfx
    ihave %Ha2 := watcherFixed_agree w0 rr rg fcs fcs0 $$ [$Hfx $Hfx0]
    ipureintro; intro _
    have : m.id = id := by rw [hmid, Ha2.1, hrg]
    simp [this, hw]
  · by_cases hid : m.id = id
    · iunfold idAssigned at Hia
      iunfold chanIdAssigned at Hca
      isimp only [hids] at Hia
      isimp only [← hmid, hid] at Hca
      ihave %Hv := ghostMapElem_agree _ _ _ _ _ _ $$ Hia Hca
      exact absurd Hv.symm hw
    · ipureintro; intro _; simp [hid, hw]

/-- The facts of the responses received, after one more. -/
theorem rcvFacts_snoc (γ : WsNames) (γc : WatchChanNames) (ms : List RespM) (r : RespM) :
    □ ([∗list] j ↦ m ∈ ms, rcvFact (GF := GF) γ γc (ms.take j) m) ∗ rcvFact γ γc ms r ⊢
      □ ([∗list] j ↦ m ∈ ms ++ [r], rcvFact γ γc ((ms ++ [r]).take j) m) := by
  iintro ⟨#Hs, #Hr⟩
  imodintro
  iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
  isplitl
  · iapply (BigSepL.bigSepL_mono (PROP := IProp GF) (l := ms)
      (Φ := fun j m => rcvFact (GF := GF) γ γc (ms.take j) m)
      (Ψ := fun j m => rcvFact (GF := GF) γ γc ((ms ++ [r]).take j) m) ?_) $$ Hs
    intro k x hk
    have hlt : k < ms.length := (List.getElem?_eq_some_iff.1 hk).1
    rw [List.take_append_of_le_length (by omega)]
  · rw [List.take_left' rfl]
    iexact Hr

/-- **Receiving on the stream's channel**: the channel's receive (`watch_recv_au`), the received
response's facts kept in the consumer's view. -/
theorem wsChan_recv_proof : wsChan_recv.law (GF := GF) := by
  intro ws γ ι
  iintro #Hst
  iunfold isMvccWatchStream at Hst
  iunfold isMvccWatchStreamI at Hst
  icases Hst with ⟨%Hn, -, -, #Hch, #Hinv, -⟩
  obtain ⟨hmv, -⟩ := Hn
  iexists ι.c.ch
  unfold wsChanOf
  iframe Hch
  iintro !> %rs %Φ Hr HΦ
  iunfold wsRecv at Hr
  iunfold wsRecvI at Hr
  icases Hr with ⟨Htok, %ms, Hcons, %Hrs, #Hfs⟩
  iapply (watch_recv_au γ.ws ι.ch ι.c ms Φ) $$ [] Hcons
  · rw [← hmv]; iexact Hinv
  iintro %v %ok Hres
  iapply HΦ
  iunfold watchRecvResult at Hres
  cases ok with
  | false =>
    isimp only [Bool.false_eq_true, ↓reduceIte] at Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    iunfold wsRecv
    iunfold wsRecvI
    iframe Htok
    iexists ms
    iframe Hres Hfs
    ipureintro; exact Hrs
  | true =>
    simp only [↓reduceIte]
    icases Hres with ⟨%r, Hcons, #Hv, #Hok, #Hro, #Hreg, #Hprog, #Hcov, #Hrat, #Hsl, %Hidx⟩
    iexists (respView r)
    isplitl [Htok Hcons]
    · iunfold wsRecv
      iunfold wsRecvI
      iframe Htok
      iexists (ms ++ [r])
      iframe Hcons
      isplitr
      · ipureintro; rw [Hrs, List.map_append]; rfl
      iapply rcvFacts_snoc
      iframe Hfs
      iunfold rcvFact
      rw [hmv]
      iframe Hok Hro Hreg Hprog Hcov Hrat Hsl
      ipureintro; exact Hidx
    · iunfold respIs at Hv
      iunfold wrespIs
      icases Hv with ⟨%Hv, %ps, #Hps, %Hlen, #Hevs⟩
      isplitr
      · ipureintro; exact Hv
      iexists ps
      simp only [respView]
      iframe Hps Hevs
      ipureintro; exact Hlen

/-- **One watcher's events** (`wsRecv_events`' first conjunct, for a watcher without filters): its
responses so far, all of them covered by its last one's receive facts (`watchRecvOk`), are its
range's events of a watched log, a prefix of the notified history. -/
theorem events_one (ι : WsNameI) (σ : MvccState) (ms : List RespM) (id : w64) (wi : WInfo)
    (hids : ι.o.ids = ι.c.ids) (hfs : wi.fs = []) :
    □ ([∗list] j ↦ m ∈ ms, rcvFact (GF := GF) ι.mv.ws ι.c (ms.take j) m) ∗ wInfoOk ι id wi ∗
      mvccStateI ι.mv σ ⊢
      ⌜∃ hi, hi ≤ σ.notifiedLog.length ∧
        recvEvs (ms.map respView) id = filtered wi.fs (watchEvents σ.notifiedLog wi.rg wi.lo hi)⌝ := by
  iintro ⟨#Hfs, #Hi, Hσ⟩
  iunfold wInfoOk at Hi
  icases Hi with ⟨%w0, %fcs0, #Hia, #Hwi, #Hfi, ⟨%Hrg, -⟩⟩
  ihave #Hwi0 := Hwi
  iunfold watcherIs at Hwi0
  icases Hwi0 with ⟨%γw0, %C, #Hmeta0, #Hfx0, -, -, %Hlo0⟩
  isimp only [hfs] at Hfi
  iunfold filtersImpl at Hfi
  icases Hfi with ⟨%fps, #Hfps, %Hfl, -⟩
  have hfps : fps = [] := List.eq_nil_of_length_eq_zero (by simpa using Hfl)
  subst hfps
  -- the view's id and its watcher agree on every response with events
  ihave %Hag : ⌜∀ m ∈ ms, m.evs ≠ [] → decide (m.id = id) = decide (m.w = w0)⌝ $$ []
  · iapply (pure_forall (PROP := IProp GF)).2
    iintro %m
    iapply (pure_wand (PROP := IProp GF)).1
    iintro %hm
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hm
    ihave #Hfj := BigSepL.bigSepL_lookup hj $$ Hfs
    iapply rcv_agree ι.mv.ws ι.o ι.c hids id w0 wi.rg fcs0 Hrg (ms.take j) m
    iframe Hia Hfx0 Hfj
  have hrecv : recvEvs (ms.map respView) id =
      ((ms.filter (fun m => decide (m.w = w0))).map RespM.evs).flatten := by
    rw [recvEvs_view]; exact flatten_filter_evs_eq ms _ _ Hag
  rw [hrecv, hfs]
  rcases last_idx ms (fun m => decide (m.w = w0)) with hnil | ⟨j, m, hj, hm, ht⟩
  · ipureintro
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [hnil, watchEvents_empty _ _ (Nat.zero_le _)]
    rfl
  ihave #Hfj := BigSepL.bigSepL_lookup hj $$ Hfs
  iunfold rcvFact at Hfj
  icases Hfj with ⟨-, #Hro, -⟩
  have hmw : m.w = w0 := by simpa using hm
  have htk : ms.take (j + 1) = ms.take j ++ [m] := by
    rw [List.take_succ, hj]; rfl
  have hrs0 : ((ms.take j ++ [m]).filter (fun x => decide (x.w = m.w))) =
      ms.filter (fun x => decide (x.w = w0)) := by
    rw [hmw, ← htk, ht]
  isimp only [hrs0] at Hro
  iunfold watchRecvOk at Hro
  icases Hro with ⟨%γw, %r, %fcs, %L, %D, %d, #Hmeta, #Hfx, -, #Hev, -, %Hpure, #HD, -⟩
  isimp only [hmw] at Hmeta Hfx
  ihave %Hm := watcherMeta_agree ι.mv.ws w0 γw γw0 $$ Hmeta Hmeta0
  ihave %Hf := watcherFixed_agree w0 r wi.rg fcs fcs0 $$ [$Hfx $Hfx0]
  obtain ⟨rfl, rfl⟩ := Hf
  subst Hm
  ihave %Hwhole := deliv_nofilter fcs D $$ [$Hfps $HD]
  ihave %Hpre := evLog_notified ι.mv σ L $$ [$Hev $Hσ]
  ipureintro
  obtain ⟨hevs, hwe, hd, -⟩ := Hpure
  have hflat : ((ms.filter (fun x => decide (x.w = w0))).map RespM.evs).flatten =
      watchEvents L wi.rg γw.lo d := by
    rw [hevs, delivs_whole D Hwhole, hwe]
  have hf0 : ∀ evs : List EvM, filtered [] evs = evs := by intro evs; unfold filtered; simp
  simp only [hf0, hflat, Hlo0.1]
  rcases hd with hd | hd
  · exact ⟨d, Nat.le_trans hd Hpre.length_le, watchEvents_prefix Hpre _ hd⟩
  · refine ⟨0, Nat.zero_le _, ?_⟩
    rw [watchEvents_empty _ _ (by rw [← Hlo0.1]; exact hd), watchEvents_empty _ _ (Nat.zero_le _)]

/-- **An event-less response's revision is of the notified history** (`wsRecv_events`' second
conjunct): its revision is the last of a notified log (`respRev`), a prefix of the client's log
(`γ.wlog`'s halves). -/
theorem rev_one (ι : WsNameI) (σ : MvccState) (pre : List RespM) (m : RespM) (hw : ι.mv.watched = true)
    (he : m.evs = []) :
    rcvFact (GF := GF) ι.mv.ws ι.c pre m ∗ mvccStateI ι.mv σ ⊢
      ⌜sint.nat m.rev < σ.notifiedLog.length⌝ := by
  iintro ⟨#Hf, Hσ⟩
  iunfold rcvFact at Hf
  icases Hf with ⟨-, -, -, -, #Hcov, -⟩
  iunfold respCov at Hcov
  icases Hcov with ⟨-, -, -, #Hrev⟩
  iunfold respRev at Hrev
  icases Hrev with (%Hne | ⟨%L, #Hlb, %HL⟩)
  · exact absurd he Hne
  iunfold mvccStateI at Hσ
  icases Hσ with ⟨-, -, -, -, -, -, Hwl, %Hreach⟩
  isimp only [hw, ↓reduceIte] at Hwl
  iunfold notifiedLb at Hlb
  ihave %Hp := mono_list_auth_lb_valid _ _ _ _ $$ Hwl Hlb
  ipureintro
  have h1 := Hp.2.length_le
  have h2 := (log_notified σ).length_le
  have h3 := HL.1
  have h4 := Hreach.1.len_ge
  have h5 : sint.nat m.rev = (sint.Z m.rev).toNat := rfl
  omega

/-- **The watch guarantee** (`wsRecv_events`). -/
theorem wsRecv_events_proof : wsRecv_events.law (GF := GF) := by
  intro ws γ ι rs W σ
  iintro ⟨#Hst, Hr, Hw, Hσ⟩
  iunfold isMvccWatchStream at Hst
  iunfold isMvccWatchStreamI at Hst
  icases Hst with ⟨%Hn, -⟩
  obtain ⟨hmv, hw, hids, -⟩ := Hn
  subst hmv
  iunfold wsRecv at Hr
  iunfold wsRecvI at Hr
  icases Hr with ⟨-, %ms, -, %Hrs, #Hfs⟩
  subst Hrs
  iunfold wsWatchers at Hw
  iunfold wsWatchersI at Hw
  icases Hw with ⟨-, -, #Hinfo⟩
  iunfold mvccState at Hσ
  ihave %H1 : ⌜∀ (id : w64) (w : WInfo), W !! id = some w → w.fs = [] → ∃ hi,
      hi ≤ σ.notifiedLog.length ∧
      recvEvs (ms.map respView) id = filtered w.fs (watchEvents σ.notifiedLog w.rg w.lo hi)⌝ $$ [Hσ]
  · iapply (pure_forall (PROP := IProp GF)).2
    iintro %id
    iapply (pure_forall (PROP := IProp GF)).2
    iintro %wi
    iapply (pure_wand (PROP := IProp GF)).1
    iintro %hW
    iapply (pure_wand (PROP := IProp GF)).1
    iintro %hfs
    ihave #Hi := BigSepM.bigSepM_lookup hW $$ Hinfo
    iapply events_one ι σ ms id wi hids hfs
    iframe Hfs Hi Hσ
  ihave %H2 : ⌜∀ r ∈ ms.map respView, r.evs = [] → sint.nat r.rev < σ.notifiedLog.length⌝ $$ [Hσ]
  · iapply (pure_forall (PROP := IProp GF)).2
    iintro %r
    iapply (pure_wand (PROP := IProp GF)).1
    iintro %hr
    iapply (pure_wand (PROP := IProp GF)).1
    iintro %he
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hr
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hm
    ihave #Hfj := BigSepL.bigSepL_lookup hj $$ Hfs
    simp only [respView] at he ⊢
    iapply rev_one ι σ (ms.take j) m hw he
    iframe Hfj Hσ
  ipureintro
  refine ⟨H1, H2, ?_⟩
  intro r hr hc
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 hr
  exact absurd rfl hc

/-- **One progress response** (`wsRecv_progress`, for a watcher without filters): the response
covers its own watcher (`respCov`) up to its revision (`covFact`), the watcher being the view's (its
id the view's, assigned by the stream to the view's watcher). -/
theorem progress_one (ι : WsNameI) (σ : MvccState) (ms : List RespM) (id : w64) (wi : WInfo)
    (j : Nat) (m : RespM) (hids : ι.o.ids = ι.c.ids) (hw : ι.mv.watched = true) (hfs : wi.fs = [])
    (hj : ms[j]? = some m) (he : m.evs = []) (hid : m.id = id) :
    □ ([∗list] j ↦ m ∈ ms, rcvFact (GF := GF) ι.mv.ws ι.c (ms.take j) m) ∗ wInfoOk ι id wi ∗
      mvccStateI ι.mv σ ⊢
      ⌜sint.nat m.rev + 1 ≤ σ.notifiedLog.length ∧
        recvEvs ((ms.map respView).take (j + 1)) id =
          filtered wi.fs (watchEvents σ.notifiedLog wi.rg wi.lo (sint.nat m.rev + 1))⌝ := by
  iintro ⟨#Hfs, #Hi, Hσ⟩
  iunfold wInfoOk at Hi
  icases Hi with ⟨%w0, %fcs0, #Hia, #Hwi, #Hfi, ⟨%Hrg, %Hidne, %Hlo1⟩⟩
  ihave #Hwi0 := Hwi
  iunfold watcherIs at Hwi0
  icases Hwi0 with ⟨%γw0, %C, #Hmeta0, #Hfx0, -, -, %Hlo0⟩
  isimp only [hfs] at Hfi
  iunfold filtersImpl at Hfi
  icases Hfi with ⟨%fps, #Hfps, %Hfl, -⟩
  have hfps : fps = [] := List.eq_nil_of_length_eq_zero (by simpa using Hfl)
  subst hfps
  ihave %Hag : ⌜∀ m ∈ ms, m.evs ≠ [] → decide (m.id = id) = decide (m.w = w0)⌝ $$ []
  · iapply (pure_forall (PROP := IProp GF)).2
    iintro %m'
    iapply (pure_wand (PROP := IProp GF)).1
    iintro %hm
    obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1 hm
    ihave #Hfj := BigSepL.bigSepL_lookup hj' $$ Hfs
    iapply rcv_agree ι.mv.ws ι.o ι.c hids id w0 wi.rg fcs0 Hrg (ms.take j') m'
    iframe Hia Hfx0 Hfj
  ihave #Hfj := BigSepL.bigSepL_lookup hj $$ Hfs
  icases persistent_entails_right (rev_one ι σ (ms.take j) m hw he) $$ [$Hfj $Hσ] with
    ⟨%Hrv, -, Hσ⟩
  ihave #Hfj' := Hfj
  iunfold rcvFact at Hfj'
  icases Hfj' with ⟨#Hok, -, #Hreg, -, #Hcov, -⟩
  -- the response's watcher is the view's
  iunfold respOk at Hok
  icases Hok with ⟨-, %rr, %fcs, #Hfx, %Hid⟩
  iunfold chanRegFact at Hreg
  icases Hreg with ⟨%rr', %fcs', #Hfx', #Hca, -⟩
  ihave %Ha1 := watcherFixed_agree m.w rr rr' fcs fcs' $$ [$Hfx $Hfx']
  obtain ⟨rfl, rfl⟩ := Ha1
  have hmid : m.id = rr.id := by
    rcases Hid.2 with h | h
    · exact h
    · exact absurd (hid ▸ h) Hidne
  iunfold idAssigned at Hia
  iunfold chanIdAssigned at Hca
  isimp only [hids] at Hia
  isimp only [← hmid, hid] at Hca
  ihave %Hww := ghostMapElem_agree _ _ _ _ _ _ $$ Hia Hca
  -- it covers itself
  iunfold respCov at Hcov
  icases Hcov with ⟨#Hcf, -, %Hin, -⟩
  ihave #Hcv := Hcf $$ %m.w %(Hin he)
  iunfold covFact at Hcv
  icases Hcv with ⟨%γw, %r, %fcs1, %D, %L, %d, #Hmeta, -, #Hfx1, #Hev, #HD, %Hc⟩
  isimp only [← Hww] at Hmeta Hfx1
  ihave %Hm := watcherMeta_agree ι.mv.ws w0 γw γw0 $$ Hmeta Hmeta0
  ihave %Hf := watcherFixed_agree w0 r wi.rg fcs1 fcs0 $$ [$Hfx1 $Hfx0]
  obtain ⟨rfl, rfl⟩ := Hf
  subst Hm
  ihave %Hwhole := deliv_nofilter fcs1 D $$ [$Hfps $HD]
  ihave %Hpre := evLog_notified ι.mv σ L $$ [$Hev $Hσ]
  ipureintro
  obtain ⟨hevs, hwe, hdL, hd1, hd2, -, hlo⟩ := Hc
  have hlo' : γw.lo = wi.lo := Hlo0.1
  have h5 : sint.nat m.rev = (sint.Z m.rev).toNat := rfl
  have hd : d = sint.nat m.rev + 1 := by omega
  refine ⟨by omega, ?_⟩
  have hf0 : ∀ evs : List EvM, filtered [] evs = evs := by intro evs; unfold filtered; simp
  rw [← List.map_take, recvEvs_view, hfs, hf0]
  have hag' : ∀ x ∈ ms.take (j + 1), x.evs ≠ [] → decide (x.id = id) = decide (x.w = w0) :=
    fun x hx => Hag x (List.mem_of_mem_take hx)
  rw [flatten_filter_evs_eq _ _ _ hag']
  have htk : ms.take (j + 1) = ms.take j ++ [m] := by rw [List.take_succ, hj]; rfl
  have hfl : (((ms.take j ++ [m]).filter (fun x => decide (x.w = w0))).map RespM.evs).flatten =
      (((ms.take j).filter (fun x => decide (x.w = w0))).map RespM.evs).flatten := by
    simp [List.filter_append, ← Hww, he]
  rw [htk, hfl, Hww, hevs, delivs_whole D Hwhole, hwe, ← hd, hlo']
  rcases hdL with hdL | hdL
  · exact watchEvents_prefix Hpre _ hdL
  · rw [watchEvents_empty _ _ (by rw [← hlo']; exact hdL),
      watchEvents_empty _ _ (by rw [← hlo']; omega)]

/-- **Progress** (`wsRecv_progress`). -/
theorem wsRecv_progress_proof : wsRecv_progress.law (GF := GF) := by
  intro ws γ ι rs W σ
  iintro ⟨#Hst, Hr, Hw, Hσ⟩
  iunfold isMvccWatchStream at Hst
  iunfold isMvccWatchStreamI at Hst
  icases Hst with ⟨%Hn, -⟩
  obtain ⟨hmv, hw, hids, -⟩ := Hn
  subst hmv
  iunfold wsRecv at Hr
  iunfold wsRecvI at Hr
  icases Hr with ⟨-, %ms, -, %Hrs, #Hfs⟩
  subst Hrs
  iunfold wsWatchers at Hw
  iunfold wsWatchersI at Hw
  icases Hw with ⟨-, -, #Hinfo⟩
  iunfold mvccState at Hσ
  iapply (pure_forall (PROP := IProp GF)).2
  iintro %j
  iapply (pure_forall (PROP := IProp GF)).2
  iintro %id
  iapply (pure_forall (PROP := IProp GF)).2
  iintro %r
  iapply (pure_forall (PROP := IProp GF)).2
  iintro %wi
  iapply (pure_wand (PROP := IProp GF)).1
  iintro %hj
  iapply (pure_wand (PROP := IProp GF)).1
  iintro %hW
  iapply (pure_wand (PROP := IProp GF)).1
  iintro %hfs
  iapply (pure_wand (PROP := IProp GF)).1
  iintro %he
  iapply (pure_wand (PROP := IProp GF)).1
  iintro -
  iapply (pure_wand (PROP := IProp GF)).1
  iintro %hid
  rw [List.getElem?_map] at hj
  obtain ⟨m, hm, rfl⟩ : ∃ m, ms[j]? = some m ∧ respView m = r := by
    cases h : ms[j]? with
    | none => rw [h] at hj; cases hj
    | some m => rw [h] at hj; exact ⟨m, rfl, Option.some.inj hj⟩
  simp only [respView] at he hid ⊢
  ihave #Hi := BigSepM.bigSepM_lookup hW $$ Hinfo
  iapply progress_one ι σ ms id wi j m hids hw hfs hm he hid
  iframe Hfs Hi Hσ

/-- **A response's events** (`wsRecv_resp`): `respOk`'s (its events at or below its revision, its
id its watcher's when it has events), `chanRegFact`'s (a watcher's id is not `-1`). -/
theorem wsRecv_resp_proof : wsRecv_resp.law (GF := GF) := by
  intro ι rs W
  iintro ⟨Hr, -⟩
  iunfold wsRecv at Hr
  iunfold wsRecvI at Hr
  icases Hr with ⟨-, %ms, -, %Hrs, #Hfs⟩
  subst Hrs
  iapply (pure_forall (PROP := IProp GF)).2
  iintro %r
  iapply (pure_wand (PROP := IProp GF)).1
  iintro %hr
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hr
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hm
  ihave #Hfj := BigSepL.bigSepL_lookup hj $$ Hfs
  iunfold rcvFact at Hfj
  icases Hfj with ⟨#Hok, -, #Hreg, -⟩
  iunfold respOk at Hok
  icases Hok with ⟨%Hmod, %rr, %fcs, #Hfx, %Hid⟩
  iunfold chanRegFact at Hreg
  icases Hreg with ⟨%rr', %fcs', #Hfx', -, %Hne⟩
  ihave %Ha := watcherFixed_agree m.w rr rr' fcs fcs' $$ [$Hfx $Hfx']
  obtain ⟨rfl, rfl⟩ := Ha
  ipureintro
  simp only [respView]
  refine ⟨Hmod, fun h => absurd rfl h, fun he => ?_⟩
  rw [Hid.1 he]; exact Hne

end laws

end mvcc
end EtcdGrove
end Perennial
