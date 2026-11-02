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

end laws

end mvcc
end EtcdGrove
end Perennial
