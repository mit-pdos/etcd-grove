/-
Proof of `Spec/Cache__applyStorage.lean`. Lean-first (no Rocq counterpart).

The loop invariant: the store's writer at a synced state `st`, the store watcher's consumer
having received `rcv`, and the store's latest map etcd's state at `Y`, the revision of the last
event received (`R` before any: `lastEvRevOr`). For the next response `r`, the watcher's
publication (`demuxPub`) gives the delivered segment's certificate chain; the events of `rcv`
and of `r` split it (no batch straddles two responses: `SentOrdered`), and its part for `r` is
`splitBatches r.events`, chained from `Y` (`storeW_chain`). Along it, `isEtcdKvs_step`
certifies every snapshot `Apply` appends, and the new latest map (`applyResp_certs`).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__applyStorage
public import Spec.go_etcd_io.etcd.cache.v3.store__Apply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

/-! ## Pure lemmas -/

theorem mem_takeWhile_rev {e x : EvModel} {l : List EvModel}
    (hx : x ∈ l.takeWhile (fun x => decide (x.rev = e.rev))) : x.rev = e.rev := by
  simpa using List.all_eq_true.1 List.all_takeWhile x hx

/-- The first batch of `splitBatches` is the run of the first event's revision. -/
theorem splitBatches_takeWhile (e : EvModel) (es : List EvModel) :
    splitBatches (e :: es) = ((e :: es).takeWhile (fun x => decide (x.rev = e.rev))) ::
      splitBatches ((e :: es).dropWhile (fun x => decide (x.rev = e.rev))) := by
  have hsplit := List.takeWhile_append_dropWhile (p := fun x => decide (x.rev = e.rev))
    (l := e :: es)
  conv => lhs; rw [← hsplit]
  have htw : (e :: es).takeWhile (fun x => decide (x.rev = e.rev)) ≠ [] := by
    simp
  rw [splitBatches_append, splitBatches_run _ htw e.rev]
  · rfl
  · intro x hx; exact mem_takeWhile_rev hx
  · intro x y hx hy
    have hx' : x.rev = e.rev := mem_takeWhile_rev (List.mem_of_getLast? hx)
    have hy' := List.head?_dropWhile_not (fun x => decide (x.rev = e.rev)) (e :: es)
    rw [hy] at hy'
    simp at hy'
    rw [hx']; exact fun h => hy' h.symm

/-- The revision of the last event of `evs`, `d` if none. -/
def lastRevW (evs : List EvModel) (d : w64) : w64 :=
  match evs.getLast? with
  | some e => e.rev
  | none => d

theorem lastRevW_cons (e : EvModel) (es : List EvModel) (d : w64) :
    lastRevW (e :: es) d = lastRevW ((e :: es).dropWhile (fun x => decide (x.rev = e.rev))) e.rev := by
  have hsplit := List.takeWhile_append_dropWhile (p := fun x => decide (x.rev = e.rev))
    (l := e :: es)
  unfold lastRevW
  conv => lhs; rw [← hsplit]
  rw [List.getLast?_append]
  cases hd : ((e :: es).dropWhile (fun x => decide (x.rev = e.rev))).getLast? with
  | some y => simp
  | none =>
    cases ht : ((e :: es).takeWhile (fun x => decide (x.rev = e.rev))).getLast? with
    | none => simp at ht
    | some x => simp [mem_takeWhile_rev (List.mem_of_getLast? ht)]

/-- Batches whose flattening is `xs ++ ys`, every event of `xs` below every event of `ys`, split
into the batches of `xs` and those of `ys`. -/
theorem batches_split : ∀ (bs : List Batch) (xs ys : List EvModel), (∀ b ∈ bs, BatchOk b) →
    bs.flatten = xs ++ ys → (∀ x ∈ xs, ∀ y ∈ ys, sint.Z x.rev < sint.Z y.rev) →
    ∃ bs1 bs2, bs = bs1 ++ bs2 ∧ bs1.flatten = xs ∧ bs2.flatten = ys := by
  intro bs
  induction bs with
  | nil =>
    intro xs ys _ h _
    simp at h
    exact ⟨[], [], rfl, h.1.symm, h.2.symm⟩
  | cons b bt ih =>
    intro xs ys hok h hlt
    by_cases hxs : xs = []
    · subst hxs; exact ⟨[], b :: bt, rfl, rfl, by simpa using h⟩
    simp only [List.flatten_cons] at h
    rcases List.append_eq_append_iff.1 h with ⟨a', hxs', hbt⟩ | ⟨c', hb, hys⟩
    · obtain ⟨bs1, bs2, h1, h2, h3⟩ := ih a' ys (fun b' hb' => hok b' (List.mem_cons_of_mem _ hb'))
        hbt (fun x hx y hy => hlt x (by rw [hxs']; exact List.mem_append_right _ hx) y hy)
      exact ⟨b :: bs1, bs2, by rw [h1]; rfl, by simp [h2, hxs'], h3⟩
    · by_cases hc : c' = []
      · subst hc
        simp at hb hys
        exact ⟨[b], bt, rfl, by simp [hb], hys.symm⟩
      · exfalso
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil xs hxs
        obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil c' hc
        have hbok := hok b List.mem_cons_self
        have h1 := hbok.2 x (by rw [hb]; exact List.mem_append_left _ hx)
        have h2 := hbok.2 y (by rw [hb]; exact List.mem_append_right _ hy)
        have := hlt x hx y (by rw [hys]; exact List.mem_append_left _ hy)
        rw [h1, h2] at this
        exact Int.lt_irrefl _ this

/-- Well-formed sorted batches are the `splitBatches` of their events. -/
theorem splitBatches_of_ok : ∀ (bs : List Batch), (∀ b ∈ bs, BatchOk b) → RevSorted batchRev bs →
    splitBatches bs.flatten = bs := by
  intro bs
  induction bs with
  | nil => intro _ _; rfl
  | cons b bt ih =>
    intro hok hs
    unfold RevSorted at hs
    rw [List.pairwise_cons] at hs
    have hb := hok b List.mem_cons_self
    simp only [List.flatten_cons]
    rw [splitBatches_append, splitBatches_run b hb.1 (batchRev b) hb.2,
      ih (fun b' hb' => hok b' (List.mem_cons_of_mem _ hb')) hs.2]
    · rfl
    · intro x y hx hy
      rw [hb.2 x (List.mem_of_getLast? hx)]
      obtain ⟨b', hb', hyb'⟩ := List.mem_flatten.1 (List.mem_of_head? hy)
      rw [(hok b' (List.mem_cons_of_mem _ hb')).2 y hyb']
      intro h
      have := hs.1 b' hb'
      rw [h] at this
      exact Int.lt_irrefl _ this

/-- The last event of well-formed batches is in the last batch. -/
theorem flatten_getLast (bs : List Batch) (hok : ∀ b ∈ bs, BatchOk b) (b : Batch)
    (h : bs.getLast? = some b) : ∃ x, bs.flatten.getLast? = some x ∧ x.rev = batchRev b := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 h
  have hb := hok b (by rw [hys]; simp)
  obtain ⟨x, hx⟩ : ∃ x, b.getLast? = some x := by
    cases hl : b.getLast? with
    | none => simp [List.getLast?_eq_none_iff] at hl; exact absurd hl hb.1
    | some x => exact ⟨x, rfl⟩
  refine ⟨x, ?_, hb.2 x (List.mem_of_getLast? hx)⟩
  rw [hys]; simp [List.getLast?_append, hx]

theorem lastEvRevOr_snoc (rcv : List RespModel) (r : RespModel) (d : Int) (Y : w64)
    (hY : sint.Z Y = lastEvRevOr rcv d) :
    lastEvRevOr (rcv ++ [r]) d = sint.Z (lastRevW r.events Y) := by
  unfold lastEvRevOr lastRevW
  rw [eventsOf_append, List.getLast?_append]
  cases h : r.events.getLast? with
  | some e => simp
  | none =>
    rw [hY]; unfold lastEvRevOr; rfl

theorem applyRespSnaps_cases (st : StoreState) (r : RespModel) :
    applyRespSnaps st r = [] ∨ applyRespSnaps st r = applyEventsSnaps st.latest r.events := by
  unfold applyRespSnaps
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem applyResp_latest (cap : Nat) (st : StoreState) (r : RespModel)
    (hok : (applyResp cap st r).2 = true) :
    (r.events = [] ∧ (applyResp cap st r).1.latest = st.latest) ∨
      applyResp cap st r = applyEvents cap st r.events := by
  unfold applyResp at hok ⊢
  by_cases h1 : r.canceled = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at hok; simp at hok
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at hok ⊢
  by_cases h2 : (!validRevisions r st.latestRev) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)] at hok; simp at hok
  rw [ite_eq_right_of_eq_false _ _ (eq_false h2)] at hok ⊢
  by_cases h3 : r.isProgressNotify = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h3)]
    left
    refine ⟨?_, by split <;> rfl⟩
    unfold RespModel.isProgressNotify at h3
    simp only [Bool.and_eq_true] at h3
    exact List.isEmpty_iff.1 h3.1.1.1.1
  rw [ite_eq_right_of_eq_false _ _ (eq_false h3)] at hok ⊢
  by_cases h4 : (!r.events.isEmpty) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h4)]; right; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h4)]
    left
    simp at h4
    exact ⟨h4, rfl⟩

theorem lastRevW_ne_nil (evs : List EvModel) (d d' : w64) (h : evs ≠ []) :
    lastRevW evs d = lastRevW evs d' := by
  unfold lastRevW
  cases hl : evs.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.1 hl) h
  | some e => rfl

/-- After a successful `applyEvents`, the latest revision is the last event's. -/
theorem applyEvents_latestRev (cap : Nat) :
    ∀ (evs : List EvModel) (st : StoreState), (applyEvents cap st evs).2 = true →
      (applyEvents cap st evs).1.latestRev = lastRevW evs st.latestRev := by
  intro evs
  induction h : evs.length using Nat.strongRecOn generalizing evs with
  | ind n ih =>
    intro st hok
    match evs with
    | [] => rw [applyEvents] at hok ⊢; rfl
    | e :: es =>
      rw [applyEvents] at hok ⊢
      rw [lastRevW_cons]
      cases hb : applyBatch st.latest ((e :: es).takeWhile (fun x => decide (x.rev = e.rev))) with
      | mk m ok =>
        rw [hb] at hok
        cases ok with
        | false => simp at hok
        | true =>
          simp only at hok ⊢
          have hlen : ((e :: es).dropWhile (fun x => decide (x.rev = e.rev))).length < n := by
            rw [← h]; exact dropWhile_length_lt e es
          exact ih _ hlen _ rfl _ hok

/-- A successful `Apply` does not lower the latest revision, and after events it is the last
event's. -/
theorem applyResp_rev (cap : Nat) (st : StoreState) (r : RespModel)
    (hok : (applyResp cap st r).2 = true) :
    sint.Z st.latestRev ≤ sint.Z (applyResp cap st r).1.latestRev ∧
      (r.events ≠ [] → (applyResp cap st r).1.latestRev = lastRevW r.events st.latestRev) := by
  unfold applyResp at hok ⊢
  by_cases h1 : r.canceled = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at hok; simp at hok
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at hok ⊢
  by_cases h2 : (!validRevisions r st.latestRev) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)] at hok; simp at hok
  rw [ite_eq_right_of_eq_false _ _ (eq_false h2)] at hok ⊢
  have hv : validRevisions r st.latestRev = true := by simpa using h2
  by_cases h3 : r.isProgressNotify = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h3)]
    have he : r.events = [] := by
      unfold RespModel.isProgressNotify at h3
      simp only [Bool.and_eq_true] at h3
      exact List.isEmpty_iff.1 h3.1.1.1.1
    refine ⟨?_, fun h => absurd he h⟩
    unfold validRevisions at hv
    rw [ite_eq_left_of_eq_true _ _ (eq_true h3)] at hv
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Int.not_lt] at hv
    split
    · exact Int.le_refl _
    · exact hv
  rw [ite_eq_right_of_eq_false _ _ (eq_false h3)] at hok ⊢
  by_cases h4 : (!r.events.isEmpty) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h4)] at hok ⊢
    have hl := applyEvents_latestRev cap r.events st hok
    refine ⟨?_, fun _ => hl⟩
    rw [hl]
    have hne : r.events ≠ [] := by simpa using h4
    unfold validRevisions at hv
    rw [ite_eq_right_of_eq_false _ _ (eq_false h3)] at hv
    simp only [List.all_eq_true, decide_eq_true_eq] at hv
    unfold lastRevW
    cases hlast : r.events.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 hlast) hne
    | some e => exact Int.le_of_lt (hv e (List.mem_of_getLast? hlast))
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h4)]
    have he : r.events = [] := by simpa using h4
    exact ⟨Int.le_refl _, fun h => absurd he h⟩

/-- A response with an event at or below `Y`, when `Y` is at most the latest revision, is not
applied: `validateRevisions` rejects it (or it is canceled), and nothing is appended. -/
theorem applyResp_stale (cap : Nat) (st : StoreState) (r : RespModel) (Y : w64)
    (hstale : ∃ e ∈ r.events, sint.Z e.rev ≤ sint.Z Y) (hY : sint.Z Y ≤ sint.Z st.latestRev) :
    applyRespSnaps st r = [] ∧ (applyResp cap st r).2 = false := by
  obtain ⟨e, he, hle⟩ := hstale
  unfold applyRespSnaps applyResp
  by_cases h1 : r.canceled = true
  · simp [h1]
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  have hnp : r.isProgressNotify = false := by
    cases hp : r.isProgressNotify
    · rfl
    · unfold RespModel.isProgressNotify at hp
      simp only [Bool.and_eq_true] at hp
      rw [List.isEmpty_iff.1 hp.1.1.1.1] at he; cases he
  have hv : validRevisions r st.latestRev = false := by
    unfold validRevisions
    rw [hnp]
    simp only [Bool.false_eq_true, ↓reduceIte, List.all_eq_false, decide_eq_true_eq, Int.not_lt]
    exact ⟨e, he, by omega⟩
  simp [hv]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- Along a certificate chain from `Y` through the batches of `evs`, with the latest map etcd's
state at `Y`, every snapshot `applyEvents` appends is etcd's state at its revision, and so is the
final latest map (at the last event's revision) when every batch applies. -/
theorem applyEvents_certs (pfx : GoString) (cap : Nat) :
    ∀ (evs : List EvModel) (st : StoreState) (Y : w64),
    isEtcdKvs (GF := GF) Y pfx st.latest ∗
      certChain (etcdStepCert pfx) (sint.Z Y) (splitBatches evs) ⊢
    snapCerts (etcdCert pfx) (applyEventsSnaps st.latest evs) ∗
      (⌜(applyEvents cap st evs).2 = true⌝ -∗
        isEtcdKvs (lastRevW evs Y) pfx (applyEvents cap st evs).1.latest) := by
  intro evs
  induction h : evs.length using Nat.strongRecOn generalizing evs with
  | ind n ih =>
    intro st Y
    match evs with
    | [] =>
      iintro ⟨#HY, -⟩
      rw [applyEventsSnaps, applyEvents]
      isplitl []
      · unfold snapCerts; imodintro; iintro %x %hx; simp at hx
      · iintro -
        simp only [lastRevW, List.getLast?_nil]
        iexact HY
    | e :: es =>
      iintro ⟨#HY, #Hch⟩
      rw [splitBatches_takeWhile, certChain_cons]
      icases Hch with ⟨⟨%p, %Hp, #Hc⟩, #Hch⟩
      have htw : (e :: es).takeWhile (fun x => decide (x.rev = e.rev)) =
          e :: es.takeWhile (fun x => decide (x.rev = e.rev)) := by
        simp
      have hbr : batchRev ((e :: es).takeWhile (fun x => decide (x.rev = e.rev))) = e.rev := by
        rw [htw]; rfl
      rw [hbr] at Hp
      rw [hbr]
      rw [applyEventsSnaps, applyEvents, lastRevW_cons]
      cases hb : applyBatch st.latest ((e :: es).takeWhile (fun x => decide (x.rev = e.rev))) with
      | mk m' ok =>
        cases ok with
        | false =>
          simp only
          isplitl []
          · unfold snapCerts; imodintro; iintro %x %hx; simp at hx
          · iintro %hf; simp at hf
        | true =>
          simp only
          have hcert : ∀ p b, (etcdStepCert (GF := GF) pfx).cert p b = etcdStepCertBody pfx p b :=
            fun _ _ => rfl
          simp only [hcert]
          iunfold etcdStepCertBody at Hc
          icases Hc with ⟨%cs, #Hm, %Hst⟩
          rw [hbr] at Hst
          ihave #HY' : isEtcdKvs e.rev pfx m' $$ []
          · iapply isEtcdKvs_step Y p e.rev pfx st.latest m' _ cs Hp Hst.1 Hst.2 hb
            iframe #
          have hlen : ((e :: es).dropWhile (fun x => decide (x.rev = e.rev))).length < n := by
            rw [← h]; exact dropWhile_length_lt e es
          icases ih _ hlen _ rfl
            { latestRev := e.rev, latest := m', history := ringAppend cap st.history (e.rev, m') }
            e.rev $$ [$HY' $Hch] with ⟨#Hs, Hl⟩
          iframe Hl
          unfold snapCerts
          imodintro
          iintro %x %hx
          rcases List.mem_cons.1 hx with rfl | hx
          · unfold etcdCert; iexact HY'
          · iapply Hs; ipureintro; exact hx

/-- What `Apply(r)` needs and leaves, given the chain of `r`'s batches from `Y` and the latest
map etcd's state at `Y`: the snapshots it appends are certified, and after a success the latest
map is etcd's state at the last event's revision (`Y` if `r` has no events). -/
theorem applyResp_certs (pfx : GoString) (cap : Nat) (st : StoreState) (r : RespModel) (Y : w64) :
    isEtcdKvs (GF := GF) Y pfx st.latest ∗
      certChain (etcdStepCert pfx) (sint.Z Y) (splitBatches r.events) ⊢
    snapCerts (etcdCert pfx) (applyRespSnaps st r) ∗
      (⌜(applyResp cap st r).2 = true⌝ -∗
        isEtcdKvs (lastRevW r.events Y) pfx (applyResp cap st r).1.latest) := by
  iintro ⟨#HY, #Hch⟩
  icases applyEvents_certs pfx cap r.events st Y $$ [$HY $Hch] with ⟨#Hs, Hl⟩
  isplitl []
  · rcases applyRespSnaps_cases st r with h | h <;> rw [h]
    · unfold snapCerts; imodintro; iintro %x %hx; simp at hx
    · iexact Hs
  iintro %hok
  rcases applyResp_latest cap st r hok with ⟨he, hl⟩ | he
  · rw [hl, he]
    simp only [lastRevW, List.getLast?_nil]
    iexact HY
  · rw [he] at hok ⊢
    iapply Hl
    ipureintro; exact hok

/-- **The store watcher's next response** `r` after `rcv`: its events are sorted; they are above
`Y`, the revision of the last event of `rcv` (`R` if none), when `rcv` has events or the watcher
started right after `R`; and when they are above `Y`, its batches are chained from `Y` by the
certificates of the watcher's publication (`demuxPub`, start `s ≤ R + 1`, no filter). -/
theorem storeW_chain (pfx : GoString) (s R Y : w64) (rcv : List RespModel) (r : RespModel)
    (hs0 : 0 < sint.Z s) (hsR : sint.Z s ≤ sint.Z R + 1)
    (hY : sint.Z Y = lastEvRevOr rcv (sint.Z R)) :
    demuxPubBody (GF := GF) (etcdStepCert pfx) none s none (rcv ++ [r]) ⊢
      ⌜EvRevSorted r.events ∧ ((eventsOf rcv ≠ [] ∨ sint.Z s = sint.Z R + 1) →
          ∀ e ∈ r.events, sint.Z Y < sint.Z e.rev)⌝ ∗
        (⌜∀ e ∈ r.events, sint.Z Y < sint.Z e.rev⌝ -∗
          certChain (etcdStepCert pfx) (sint.Z Y) (splitBatches r.events)) := by
  iintro H
  iunfold demuxPubBody at H
  icases H with ⟨%s', %v, %p₀, %Hpure, #Hch⟩
  obtain ⟨hs, hD, hp, -⟩ := Hpure
  have hs' : s' = s := by
    rcases hs with hs | hs
    · exfalso; rw [hs] at hs0; exact absurd hs0 (by decide)
    · exact hs
  subst hs'
  have hp0 : p₀ < sint.Z s' := by
    rcases hp with hp | hp
    · exfalso; rw [hp] at hs0; exact absurd hs0 (by decide)
    · exact hp
  -- the segment
  have hsub : List.Sublist (streamRange s' v.n v.stream) v.stream := List.filter_sublist
  have hsegok := hD.stream_ok.sublist hsub
  have hev : (streamRange s' v.n v.stream).flatten = eventsOf rcv ++ r.events := by
    have := hD.events
    rw [eventsOf_append] at this
    rw [this]
    have hk : keepEv none = fun _ => true := rfl
    rw [hk]
    exact (List.filter_eq_self.2 (fun _ _ => rfl)).symm
  have hord : ∀ x ∈ eventsOf rcv, ∀ y ∈ r.events, sint.Z x.rev < sint.Z y.rev := by
    intro x hx y hy
    obtain ⟨evs, hevs, hxe⟩ := List.mem_flatten.1 hx
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hevs
    have hpw := hD.ordered.1
    rw [List.pairwise_append] at hpw
    exact (hpw.2.2 r' hr' r (by simp)).1 x hxe y hy
  obtain ⟨seg1, seg2, hseg, h1, h2⟩ := batches_split _ (eventsOf rcv) r.events
    hsegok.batches hev hord
  have hok2 : ∀ b ∈ seg2, BatchOk b := fun b hb =>
    hsegok.batches b (by rw [hseg]; exact List.mem_append_right _ hb)
  have hsorted2 : RevSorted batchRev seg2 := by
    have := hsegok.sorted
    rw [hseg] at this
    exact this.sublist (List.sublist_append_right _ _)
  have hseg2 : splitBatches r.events = seg2 := by
    rw [← h2]; exact splitBatches_of_ok seg2 hok2 hsorted2
  -- every event of `r` is at or above the start
  have hge : ∀ y ∈ r.events, sint.Z s' ≤ sint.Z y.rev := by
    intro y hy
    rw [← h2] at hy
    obtain ⟨b, hbm, hyb⟩ := List.mem_flatten.1 hy
    rw [(hok2 b hbm).2 y hyb]
    exact (streamRange_mem (show b ∈ streamRange s' v.n v.stream by
      rw [hseg]; exact List.mem_append_right _ hbm)).2.1
  isplitr
  · ipureintro
    refine ⟨hD.ordered.2 r (by simp), fun hc y hy => ?_⟩
    rw [hY]
    unfold lastEvRevOr
    cases hl : (eventsOf rcv).getLast? with
    | none =>
      simp only
      rcases hc with hc | hc
      · exact absurd (List.getLast?_eq_none_iff.1 hl) hc
      · have := hge y hy; omega
    | some x =>
      simp only
      exact hord x (List.mem_of_getLast? hl) y hy
  iintro %habove
  rw [hseg2]
  rw [hseg]
  icases (certChain_append (C := etcdStepCert pfx) p₀ seg1 seg2).1 $$ Hch with ⟨-, #Hch2⟩
  iapply certChain_mono_start _ _ seg2 ?_ ?_ $$ Hch2
  · -- `chainEnd p₀ seg1 ≤ Y`
    rw [hY]
    unfold chainEnd lastEvRevOr
    cases hl : seg1.getLast? with
    | none =>
      have : seg1 = [] := List.getLast?_eq_none_iff.1 hl
      subst this
      have he : eventsOf rcv = [] := by rw [← h1]; rfl
      rw [he]
      simp only [List.getLast?_nil]
      omega
    | some b =>
      obtain ⟨x, hx, hxr⟩ := flatten_getLast seg1
        (fun b hb => hsegok.batches b (by rw [hseg]; exact List.mem_append_left _ hb)) b hl
      rw [h1] at hx
      simp only [hx, hxr]
      exact Int.le_refl _
  · -- every batch of `r` is above `Y`
    intro b hb
    have hbm : b ∈ seg2 := List.mem_of_head? hb
    have hbok := hok2 b hbm
    obtain ⟨y, ys, hyb⟩ := List.exists_cons_of_ne_nil hbok.1
    have hy : y ∈ r.events := by
      rw [← h2]; exact List.mem_flatten.2 ⟨b, hbm, by rw [hyb]; exact List.mem_cons_self⟩
    have hyr : batchRev b = y.rev := by rw [hyb]; rfl
    rw [hyr]
    exact habove y hy

theorem Cache.applyStorage.wp_proof
    (wp_Apply : store.Apply.spec (GF := GF) (hG := hG)) :
    Cache.applyStorage.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap w γw sw R st0
  wp_start as ⟨#Hc, #Hw, Hcons, Hwr, #HY, %Hpure⟩
  obtain ⟨hsync, hs0, hsR, hsR'⟩ := Hpure
  ihave #Hc' := Hc
  iunfold isCacheFields at Hc'
  iNamed Hc'
  icases HisICtx with ⟨%ics, #Hctx⟩
  unfold context.isContext context.isContextDef
  iNamed Hctx
  ihave #Hw' := Hw
  iunfold isWatcher at Hw'
  iNamed Hw'
  wp_auto
  ihave HI : (∃ (st : StoreState) (rcv : List RespModel) (Y : w64),
      storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) st ∗ watcherConsumer γw rcv ∗
      isEtcdKvs Y cf.pfx st.latest ∗
      ⌜st.Synced ∧ sint.Z Y = lastEvRevOr rcv (sint.Z R) ∧ sint.Z R ≤ sint.Z Y ∧
        (eventsOf rcv ≠ [] ∨ sint.Z sw = sint.Z R + 1 ∨ sint.Z Y ≤ sint.Z st.latestRev) ∧
        (sint.Z R ≤ sint.Z st0.latestRev → sint.Z Y ≤ sint.Z st.latestRev)⌝ :
      IProp GF) $$ [Hcons Hwr]
  · iexists st0, [], R
    iframe
    iframe #
    ipureintro
    refine ⟨hsync, rfl, Int.le_refl _, ?_, id⟩
    rcases hsR' with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  wp_for HI
  icases HI with ⟨Hwr, Hcons, #HYc, %Hinv⟩
  obtain ⟨hsyncc, hYc, hRY, hcase, hlat⟩ := Hinv
  wp_apply HDone as %ch1 %γ1 #Hdone
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-c.internalCtx.Done()`: return `nil`
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro -
    wp_auto
    wp_for_post
    iapply HΦ
    iexists st
    iframe Hwr
    iintro -
    iexists Y
    iframe HYc
    ipureintro; exact ⟨hsyncc, hRY, hlat⟩
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `resp, ok := <-storeW.respCh`
    simp only [chan.blockingClausePre]
    iexists go_etcd_io.etcd.client.v3.WatchResponse, inferInstance, inferInstance, inferInstance,
      inferInstance, ch, γw.ch
    isplit
    · ipureintro; rfl
    isplit
    · iexact HisCh
    iapply watcher_recv_au w ch γw none _ rcv _ $$ Hw HrespCh Hcons
    iintro %resp %ok Hres
    iunfold watcherRecvResult at Hres
    cases ok with
    | false =>
      -- the channel is closed: return `nil`
      wp_auto
      wp_for_post
      iapply HΦ
      iexists st
      iframe Hwr
      iintro -
      iexists Y
      iframe HYc
      ipureintro; exact ⟨hsyncc, hRY, hlat⟩
    | true =>
      simp only [↓reduceIte]
      icases Hres with ⟨%r, #Hsent, Hcons, #Hpub⟩
      have hpub : (demuxPub (etcdStepCert (GF := GF) cf.pfx) none sw).pub =
          demuxPubBody (etcdStepCert cf.pfx) none sw := rfl
      simp only [hpub]
      icases storeW_chain cf.pfx sw R Y rcv r hs0 hsR hYc $$ Hpub with ⟨%Hsorted, Hchain⟩
      obtain ⟨hsorted, habove0⟩ := Hsorted
      iunfold respSent at Hsent
      icases Hsent with ⟨#Hresp, -⟩
      by_cases habove : ∀ e ∈ r.events, sint.Z Y < sint.Z e.rev
      rotate_left
      · -- an event at or below `Y`: `Apply` rejects the response
        have hYl : sint.Z Y ≤ sint.Z st.latestRev := by
          rcases hcase with h | h | h
          · exact absurd (habove0 (Or.inl h)) habove
          · exact absurd (habove0 (Or.inr h)) habove
          · exact h
        have hstale : ∃ e ∈ r.events, sint.Z e.rev ≤ sint.Z Y := by
          refine Classical.byContradiction fun hn => habove fun e he => ?_
          exact Classical.byContradiction fun h' => hn ⟨e, he, by omega⟩
        obtain ⟨hsn, hfail⟩ := applyResp_stale cf.scap st r Y hstale hYl
        wp_auto
        wp_apply wp_Apply cf.store cf.γs cf.scap (etcdCert cf.pfx) st resp r
          $$ [$HisStore $Hwr $Hresp] as %err ⟨Hwr, -, %Herr⟩
        · isplitr
          · ipureintro; exact hsorted
          rw [hsn]
          unfold snapCerts; imodintro; iintro %x %hx; simp at hx
        rw [hfail] at Herr
        obtain ⟨e, rfl⟩ := Herr
        wp_auto
        wp_for_post
        iapply HΦ
        iexists _
        iframe Hwr
        iintro %h; cases h
      ihave #Hch := Hchain $$ %habove
      icases applyResp_certs cf.pfx cf.scap st r Y $$ [$HYc $Hch] with ⟨#Hsnaps, Hlat⟩
      wp_auto
      wp_apply wp_Apply cf.store cf.γs cf.scap (etcdCert cf.pfx) st resp r
        $$ [$HisStore $Hwr $Hresp $Hsnaps] as %err ⟨Hwr, -, %Herr⟩
      · ipureintro; exact hsorted
      cases hok : (applyResp cf.scap st r).2 with
      | false =>
        rw [hok] at Herr
        obtain ⟨e, rfl⟩ := Herr
        wp_auto
        wp_for_post
        iapply HΦ
        iexists _
        iframe Hwr
        iintro %h; cases h
      | true =>
        rw [hok] at Herr
        subst Herr
        ihave #HY' := Hlat $$ []
        · ipureintro; rfl
        obtain ⟨hmono, hlast⟩ := applyResp_rev cf.scap st r hok
        wp_auto
        wp_for_post
        iframe
        iexists (applyResp cf.scap st r).1, rcv ++ [r], lastRevW r.events Y
        iframe
        iframe #
        ipureintro
        refine ⟨applyResp_synced _ _ _ hsyncc hok, (lastEvRevOr_snoc rcv r _ Y hYc).symm, ?_, ?_, ?_⟩
        · by_cases he : r.events = []
          · rw [he]; exact hRY
          · unfold lastRevW
            cases hl : r.events.getLast? with
            | none => exact absurd (List.getLast?_eq_none_iff.1 hl) he
            | some e => have := habove e (List.mem_of_getLast? hl); simp only; omega
        · by_cases he : r.events = []
          · rw [he]
            rcases hcase with h | h | h
            · left; rw [eventsOf_append]; simpa [he] using h
            · right; left; exact h
            · right; right; simp only [lastRevW, List.getLast?_nil]; omega
          · left; rw [eventsOf_append]; simp [he]
        · intro h0
          by_cases he : r.events = []
          · rw [he]; simp only [lastRevW, List.getLast?_nil]; have := hlat h0; omega
          · rw [hlast he, lastRevW_ne_nil r.events Y st.latestRev he]; exact Int.le_refl _
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
