/-
**A send's delivery facts over the API's history** (stage 2 of the mvcc API proof, the watch chain:
`notes/mvcc-api-invariants.md`, "Hand-off: stage 2, the sends' bounds"; 2026-11-05). Lean-first (no
Rocq counterpart).

A sent response's fact (`api.sent.SentFact.holds`) is stated at one lower bound `L` of the API's
notified log and one lower bound `c0` of its compaction revision, the bounds the send records
(`api.sent.evTok`). The channel invariant's facts come each with their own bounds: a watcher's
delivery (`evsWf`, its watched log's, `evLog_nlLb`), a covered watcher's (`covFact`), a doomed
watcher's witness (`doomed`), the response's revision (`revApi`). A **delivery certificate**
(`delivCert a P`) is a pair of such bounds `(L', c')` with a property `P` true at every larger pair;
two certificates join (`delivCert_join`: the two lower bounds of the notified log are comparable,
the larger compaction bound is kept), so a send gathers all of its facts at one pair.

- `deliv_sent_flatten` (pure): a watcher's sent events are its delivered events, filtered.
- `watchEvents_transfer` (pure): a watched log's range events at a revision are a longer log's.
- `evsWf_cert`: a delivery's events, filtered, are the range's of `[lo, hi)` of every larger log
  while `onceUpTo` holds (exact: transfer; doomed: the witness makes it vacuous).
- `covFact_cert`: a covered watcher's events up to the response's revision, likewise.
- `revApi_cert`: the response's revision is below every larger log's length.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## Pure -/

theorem filtered_append (fs : List (EvM → Bool)) (a b : List EvM) :
    filtered fs (a ++ b) = filtered fs a ++ filtered fs b := by
  unfold filtered; exact List.filter_append ..

/-- **A watcher's sent events are its delivered events, filtered** (each delivery filtered by the
same predicates; one not sent had all its events filtered out). -/
theorem deliv_sent_flatten (fs : List (EvM → Bool)) :
    ∀ D : List Deliv, (∀ dl ∈ D, dl.2 = filtered fs dl.1) →
      ((D.filter Deliv.sent).map Prod.snd).flatten = filtered fs (D.map Prod.fst).flatten
  | [], _ => rfl
  | dl :: D, h => by
    have ih := deliv_sent_flatten fs D (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have hdl := h dl (List.mem_cons_self ..)
    simp only [List.map_cons, List.flatten_cons, filtered_append, List.filter_cons]
    by_cases hs : Deliv.sent dl = true
    · simp only [hs, ↓reduceIte, List.map_cons, List.flatten_cons]
      rw [ih, hdl]
    · simp only [hs, Bool.false_eq_true, ↓reduceIte]
      have h2 : dl.2 = [] := by
        unfold Deliv.sent at hs
        cases h2 : dl.2 with
        | nil => rfl
        | cons _ _ => simp [h2] at hs
      rw [ih, ← hdl, h2, List.nil_append]

/-- **A watched log's events at a revision are a longer log's** (none past the watcher's first
revision, `d ≤ lo`). -/
theorem watchEvents_transfer {L' L : Log} (hp : L' <+: L) (r : WatchRange) {lo d : Nat}
    (hd : d ≤ L'.length ∨ d ≤ lo) :
    ∃ hi, hi ≤ L.length ∧ watchEvents L' r lo d = watchEvents L r lo hi := by
  rcases hd with hd | hd
  · exact ⟨d, Nat.le_trans hd hp.length_le, watchEvents_prefix hp r hd⟩
  · exact ⟨0, Nat.zero_le _, by
      rw [watchEvents_empty _ _ hd, watchEvents_empty _ _ (Nat.zero_le _)]⟩

/-! ## Delivery certificates -/

section cert
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A delivery certificate** (persistent; see the file header): lower bounds `L'` of the API's
notified log and `c'` of its compaction revision (`-1`: none needed), and `P` at every larger
pair. -/
def delivCert (a : api.AbsNames) (P : Log → Int → Prop) : IProp GF :=
  iprop(∃ (L' : Log) (c' : Int), api.nlLb a L' ∗ (⌜c' = -1⌝ ∨ api.crevAtLeast a c') ∗
    ⌜∀ L c0, L' <+: L → c' ≤ c0 → P L c0⌝)

instance delivCert_persistent (a : api.AbsNames) (P : Log → Int → Prop) :
    Persistent (delivCert (GF := GF) a P) := by
  unfold delivCert; infer_instance

theorem delivCert_mono (a : api.AbsNames) {P Q : Log → Int → Prop}
    (h : ∀ L c, P L c → Q L c) : delivCert (GF := GF) a P ⊢ delivCert a Q := by
  unfold delivCert
  iintro ⟨%L', %c', #Hn, #Hc, %hP⟩
  iexists L', c'
  iframe Hn Hc
  ipureintro; exact fun L c0 h1 h2 => h L c0 (hP L c0 h1 h2)

/-- **Two certificates join** at the longer notified-log bound and the larger compaction bound. -/
theorem delivCert_join (a : api.AbsNames) (P Q : Log → Int → Prop) :
    delivCert (GF := GF) a P ∗ delivCert a Q ⊢ delivCert a (fun L c => P L c ∧ Q L c) := by
  unfold delivCert
  iintro ⟨⟨%L1, %c1, #Hn1, #Hc1, %hP⟩, ⟨%L2, %c2, #Hn2, #Hc2, %hQ⟩⟩
  unfold api.nlLb
  ihave %hcmp := mono_list_lb_valid a.nl L1 L2 $$ Hn1 Hn2
  -- the longer notified-log bound
  ihave #Hn : (∃ L3 : Log, monoListLbOwn a.nl L3 ∗ ⌜L1 <+: L3 ∧ L2 <+: L3⌝) $$ []
  · rcases hcmp with h | h
    · iexists L2; iframe Hn2; ipureintro; exact ⟨h, List.prefix_refl _⟩
    · iexists L1; iframe Hn1; ipureintro; exact ⟨List.prefix_refl _, h⟩
  icases Hn with ⟨%L3, #Hn3, %h3⟩
  iexists L3, max c1 c2
  iframe Hn3
  isplitl
  · by_cases hc : c1 ≤ c2
    · rw [Int.max_eq_right hc]; iexact Hc2
    · rw [Int.max_eq_left (by omega)]; iexact Hc1
  · ipureintro
    intro L c0 hL hc
    exact ⟨hP L c0 (h3.1.trans hL) (by omega), hQ L c0 (h3.2.trans hL) (by omega)⟩

/-- A certificate's pair. -/
theorem delivCert_elim (a : api.AbsNames) (P : Log → Int → Prop) :
    delivCert (GF := GF) a P ⊢ ∃ (L : Log) (c0 : Int), api.nlLb a L ∗
      (⌜c0 = -1⌝ ∨ api.crevAtLeast a c0) ∗ ⌜P L c0⌝ := by
  unfold delivCert
  iintro ⟨%L', %c', #Hn, #Hc, %hP⟩
  iexists L', c'
  iframe Hn Hc
  ipureintro; exact hP L' c' (List.prefix_refl _) (Int.le_refl _)

/-- **The response's revision is one of every larger log's** (`revApi`). -/
theorem revApi_cert (γ : WsNames) (rev : w64) :
    revApi (GF := GF) γ rev ⊢ delivCert γ.st.api (fun L _ => sint.nat rev < L.length) := by
  unfold revApi delivCert
  iintro ⟨%N, #Hn, %h⟩
  iexists N, -1
  iframe Hn
  isplitl
  · ileft; ipureintro; rfl
  · ipureintro; intro L c0 hL _; exact Nat.lt_of_lt_of_le h hL.length_le

/-- **A delivery's certificate**: its events, filtered, are the range's of `[lo, hi)` of every
larger log while the revisions `[lo, c0]` change each key once (exact: `watchEvents_transfer`;
doomed: the witness's bounds make it vacuous). -/
theorem evsWf_cert (γ : WsNames) (r : WatchRange) (lo : Nat) (evs : List EvM) (d : Nat)
    (fs : List (EvM → Bool)) :
    evsWf (GF := GF) γ r lo evs d ⊢ delivCert γ.st.api (fun L c0 => api.onceUpTo L lo c0 →
      ∃ hi, hi ≤ L.length ∧ filtered fs evs = filtered fs (watchEvents L r lo hi)) := by
  unfold evsWf
  iintro ⟨%L', #HL, -, %Hb, (%he | ⟨#Hd, -⟩)⟩
  · ihave #Hn := evLog_nlLb γ.st L' $$ HL
    unfold delivCert
    iexists L', -1
    iframe Hn
    isplitl
    · ileft; ipureintro; rfl
    · ipureintro
      intro L c0 hL _ _
      obtain ⟨hi, hhi, heq⟩ := watchEvents_transfer hL r Hb
      exact ⟨hi, hhi, by rw [he, heq]⟩
  · unfold doomed
    icases Hd with ⟨%N, %c, #Hn, #Hc, %hn⟩
    unfold delivCert
    iexists N, c
    iframe Hn
    isplitl
    · iright; iexact Hc
    · ipureintro
      intro L c0 hL hc hon
      exact absurd (api.sent.onceUpTo_mono hL hc hon) hn

/-- **A covered watcher's certificate** (`covFact`, its revision `rev` not negative): its
deliveries' events are the range's of `[lo, rev + 1)` of every larger log while the revisions
`[lo, c0]` change each key once. -/
theorem covFact_cert (γ : WsNames) (γc : WatchChanNames) (pre : List RespM) (w' : Loc) (rev : w64)
    (hrev : 0 ≤ sint.Z rev) :
    covFact (GF := GF) γ γc pre w' rev ⊢ ∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice)
      (D : List Deliv),
      watcherMeta γ w' γw ∗ ⌜γw.wc = γc⌝ ∗ watcherFixed w' r fcs ∗
      □ (∀ dl : Deliv, ⌜dl ∈ D⌝ -∗ ∃ fs, filtersImpl fcs fs ∗ api.savedFilters γw.fg fs ∗
        ⌜dl.2 = filtered fs dl.1⌝) ∗
      ⌜(pre.filter (fun y => decide (y.w = w'))).map RespM.evs = (D.filter Deliv.sent).map Prod.snd ∧
        startLo r γw.lo⌝ ∗
      delivCert γ.st.api (fun L c0 => api.onceUpTo L γw.lo c0 →
        (D.map Prod.fst).flatten = watchEvents L r γw.lo (sint.nat rev + 1)) := by
  unfold covFact
  iintro ⟨%γw, %r, %fcs, %D, %L', %d, #Hm, %Hwc, #Hf, #HL, #HD, Hex, %Hp⟩
  obtain ⟨hD, hb, h1, h2, hslo, hlo⟩ := Hp
  iexists γw, r, fcs, D
  iframe Hm Hf HD
  isplitr
  · ipureintro; exact Hwc
  isplitr
  · ipureintro; exact ⟨hD, hslo⟩
  have hnat : ((sint.nat rev + 1 : Nat) : Int) = sint.Z rev + 1 := by
    show (((sint.Z rev).toNat + 1 : Nat) : Int) = _; omega
  icases Hex with (%he | #Hd)
  · ihave #Hn := evLog_nlLb γ.st L' $$ HL
    unfold delivCert
    iexists L', -1
    iframe Hn
    isplitl
    · ileft; ipureintro; rfl
    · ipureintro
      intro L c0 hL _ _
      rw [he]
      by_cases hdlo : d ≤ γw.lo
      · rw [watchEvents_empty _ _ hdlo, watchEvents_empty _ _ (by omega)]
      · have hd : d = sint.nat rev + 1 := by omega
        have hdL : d ≤ L'.length := hb.resolve_right hdlo
        rw [← hd]; exact watchEvents_prefix hL r hdL
  · unfold doomed
    icases Hd with ⟨%N, %c, #Hn, #Hc, %hn⟩
    unfold delivCert
    iexists N, c
    iframe Hn
    isplitl
    · iright; iexact Hc
    · ipureintro
      intro L c0 hL hc hon
      exact absurd (api.sent.onceUpTo_mono hL hc hon) hn

/-- **A registered watcher's sent events, over the API's history** (from its entry in the channel's
invariant, `chanWatcher`, and its saved filters `fs0`): the events sent for `w`, in order, are its
filters' kept events of the range's of `[lo, hi)` of every larger log while the revisions `[lo,
c0]` change each key once; and they are positive. -/
theorem chanWatcher_cert (γ : WsNames) (γc : WatchChanNames) (closed : Bool) (sent : List RespM)
    (w : Loc) (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice) (fs0 : List (EvM → Bool)) :
    chanWatcher (GF := GF) γ γc closed sent w ∗ watcherMeta γ w γw ∗ watcherFixed w r fcs ∗
      api.savedFilters γw.fg fs0 ⊢
      chanWatcher γ γc closed sent w ∗
      delivCert γ.st.api (fun L c0 => api.onceUpTo L γw.lo c0 → ∃ hi, hi ≤ L.length ∧
        ((sent.filter (fun x => decide (x.w = w))).map RespM.evs).flatten =
          filtered fs0 (watchEvents L r γw.lo hi)) ∗
      ⌜∀ ev ∈ ((sent.filter (fun x => decide (x.w = w))).map RespM.evs).flatten, evPos ev⌝ := by
  iintro ⟨Hcw, #Hm, #Hf, #Hsf⟩
  iunfold chanWatcher at Hcw
  icases Hcw with ⟨%γw', %r', %fcs', %evsw, %D, %d, #Hm', %Hwc, %Hslo, #Hf', Ha, %HD, #HDf,
    #Hwf, Hlc⟩
  ihave %Hγ := watcherMeta_agree _ _ _ _ $$ Hm Hm'
  subst Hγ
  ihave %Hfx := watcherFixed_agree w r r' fcs fcs' $$ [$Hf $Hf']
  obtain ⟨rfl, rfl⟩ := Hfx
  icases HDf with ⟨#HDl, #HDc⟩
  -- every delivery filtered by the saved predicates
  ihave %HDfs : ⌜∀ dl ∈ D, dl.2 = filtered fs0 dl.1⌝ $$ []
  · iapply pure_forall.2; iintro %dl
    iapply pure_forall.2; iintro %hdl
    icases BigSepL.bigSepL_mem_acc hdl $$ HDl with ⟨Hdl, -⟩
    icases Hdl with ⟨%fs, -, #Hsf', %hfs⟩
    ihave %hag := api.savedFilters_agree γw.fg fs fs0 $$ [$Hsf' $Hsf]
    ipureintro; rw [hfs, hag]
  have hsent : ((sent.filter (fun x => decide (x.w = w))).map RespM.evs).flatten = filtered fs0 evsw := by
    rw [HD.2, deliv_sent_flatten fs0 D HDfs, HD.1]
  ihave #Hc := evsWf_cert γ r γw.lo evsw d fs0 $$ Hwf
  ihave %Hpos := evsWf_pos γ r γw.lo evsw d $$ Hwf
  isplitl [Ha Hlc]
  · iunfold chanWatcher
    iexists γw, r, fcs, evsw, D, d
    iframe Hm Hf Ha Hwf Hlc
    isplitr
    · ipureintro; exact Hwc
    isplitr
    · ipureintro; exact Hslo
    isplitr
    · ipureintro; exact HD
    iintro !>
    iframe HDl
    iexact HDc
  isplitl
  · rw [hsent]; iexact Hc
  · ipureintro; rw [hsent]; exact filtered_pos fs0 evsw Hpos

end cert

end mvcc
end EtcdGrove
end Perennial
