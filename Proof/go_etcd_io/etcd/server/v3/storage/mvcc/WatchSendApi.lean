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
- `chanWatcher_cert`, `covFact_recv`: a registered watcher's sent events (all, or those before a
  response covering it), by its saved filters, over every larger log.
- `holds_own`, `holds_cmp`, `holds_all` (pure): a send's `SentFact.holds` from those facts, for each
  kind of response.
- `chanApi_send_resp` (`watcher.send`), `chanApi_send_cmp` (`cmp_send_inner`): **a send's step of
  the stream's history**, its premises (`stepOk`) assembled from the above: the registry info from
  the watcher's registration token (`chanRegW`, the channel invariant's, `stepOk_own`), a `-1`
  response's stamps from the history's registration witnesses (`regWit`: every registration a
  watcher of the channel, so covered or cancelled, `stamps_of`, `stepOk_all`), the covered watchers'
  certificates joined (`cov_certs`). In place of the placeholder `chanApi_send_M1` (2026-11-05).
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

/-! ## A send's fact, from its parts (pure) -/

/-- **A watcher's own response's fact** (`watcher.send`'s, id its watcher's): its shape from the
response's own facts and `rev < |L|`; its delivery and, without events, its progress, from the
certificates; without events, its revision at least its watcher's first less one (`covFact`) and
every earlier event-less response's (`respRev`). -/
theorem holds_own (pre : List api.WResp) (r : api.WResp) (rg : WatchRange) (fs : List (EvM → Bool))
    (lo : Nat) (L : Log) (c0 : Int) (dead : List w64)
    (hid : r.id ≠ W64 (-1)) (hc : r.compactRev = W64 0)
    (hle : ∀ ev ∈ r.evs, sint.Z ev.kv.modRev ≤ sint.Z r.rev)
    (hrev : sint.nat r.rev < L.length) (hpos : ∀ ev ∈ r.evs, evPos ev)
    (hdel : api.onceUpTo L lo c0 → ∃ hi, hi ≤ L.length ∧
      api.recvEvs (pre ++ [r]) r.id = filtered fs (watchEvents L rg lo hi))
    (hprog : r.evs = [] → api.onceUpTo L lo c0 →
      api.recvEvs (pre ++ [r]) r.id = filtered fs (watchEvents L rg lo (sint.nat r.rev + 1)))
    (hlo : r.evs = [] → (lo : Int) ≤ sint.Z r.rev + 1)
    (hmono : r.evs = [] → ∀ y ∈ pre, y.evs = [] → sint.Z y.rev ≤ sint.Z r.rev) :
    api.sent.SentFact.holds pre ⟨r, rg, fs, lo, L, c0, [], dead⟩ := by
  refine ⟨⟨hle, fun _ => hrev, fun h => absurd hc h, fun h => absurd h hid, hpos⟩,
    fun _ hon => hdel hon, fun _ he _ hon => hprog he hon, fun h => absurd h hid,
    fun he _ => ⟨fun _ => hlo he, fun h => absurd h hid, hmono he⟩⟩

/-- **A compaction response's fact** (`chooseAll`'s: no events, revision `0`, its watcher's id): its
shape from its compaction revision's bounds; its delivery from the certificate. -/
theorem holds_cmp (pre : List api.WResp) (r : api.WResp) (rg : WatchRange) (fs : List (EvM → Bool))
    (lo : Nat) (L : Log) (c0 : Int) (dead : List w64)
    (hid : r.id ≠ W64 (-1)) (hc : r.compactRev ≠ W64 0) (he : r.evs = []) (hr : r.rev = W64 0)
    (hc1 : 0 < sint.Z r.compactRev) (hc2 : sint.Z r.compactRev ≤ c0)
    (hdel : api.onceUpTo L lo c0 → ∃ hi, hi ≤ L.length ∧
      api.recvEvs (pre ++ [r]) r.id = filtered fs (watchEvents L rg lo hi)) :
    api.sent.SentFact.holds pre ⟨r, rg, fs, lo, L, c0, [], dead⟩ := by
  refine ⟨⟨fun ev hev => by simp [he] at hev, fun h => absurd h hc,
    fun _ => ⟨he, hid, hr, hc1, hc2⟩, fun h => absurd h hid, fun ev hev => by simp [he] at hev⟩,
    fun _ hon => hdel hon, fun _ _ h => absurd h hc, fun h => absurd h hid, fun _ h => absurd h hc⟩

/-- **A stream-wide (`-1`) progress response's fact** (`progressAll`'s): its shape from its
completeness facts and `rev < |L|`; each covered watcher's events up to its revision from the
certificates; its revision at least each covered watcher's first less one (`covEntry`) and every
earlier event-less response's (`respRev`). -/
theorem holds_all (pre : List api.WResp) (r : api.WResp) (L : Log) (c0 : Int)
    (cov : List api.sent.CovEntry) (dead : List w64) (rg : WatchRange) (fs : List (EvM → Bool))
    (lo : Nat) (hid : r.id = W64 (-1)) (he : r.evs = []) (hc : r.compactRev = W64 0)
    (h1 : 1 ≤ sint.Z r.rev) (hrev : sint.nat r.rev < L.length)
    (hcov : ∀ c ∈ cov, api.onceUpTo L c.lo c0 →
      api.recvEvs (pre ++ [r]) c.id = filtered c.fs (watchEvents L c.rg c.lo (sint.nat r.rev + 1)))
    (hlo : ∀ c ∈ cov, (c.lo : Int) ≤ sint.Z r.rev + 1)
    (hmono : ∀ y ∈ pre, y.evs = [] → sint.Z y.rev ≤ sint.Z r.rev) :
    api.sent.SentFact.holds pre ⟨r, rg, fs, lo, L, c0, cov, dead⟩ := by
  refine ⟨⟨fun ev hev => by simp [he] at hev, fun _ => hrev, fun h => absurd hc h,
    fun _ => ⟨he, hc, h1⟩, fun ev hev => by simp [he] at hev⟩,
    fun h => absurd hid h, fun h => absurd hid h, fun _ => hcov,
    fun _ _ => ⟨fun h => absurd hid h, fun _ => hlo, hmono⟩⟩

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

/-- **A covered watcher's sent events up to the response's revision, over the API's history**
(`covFact`, with its saved filters `fs0`): the events sent for `w'` before the response are its
filters' kept events of the range's of `[lo, rev + 1)` of every larger log while the revisions
`[lo, c0]` change each key once. -/
theorem covFact_recv (γ : WsNames) (γc : WatchChanNames) (pre : List RespM) (w' : Loc) (rev : w64)
    (hrev : 0 ≤ sint.Z rev) (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice)
    (fs0 : List (EvM → Bool)) :
    covFact (GF := GF) γ γc pre w' rev ∗ watcherMeta γ w' γw ∗ watcherFixed w' r fcs ∗
      api.savedFilters γw.fg fs0 ⊢
      delivCert γ.st.api (fun L c0 => api.onceUpTo L γw.lo c0 →
        ((pre.filter (fun y => decide (y.w = w'))).map RespM.evs).flatten =
          filtered fs0 (watchEvents L r γw.lo (sint.nat rev + 1))) := by
  iintro ⟨#Hcf, #Hm, #Hf, #Hsf⟩
  icases covFact_cert γ γc pre w' rev hrev $$ Hcf with
    ⟨%γw', %r', %fcs', %D, #Hm', -, #Hf', #HD, %Hp, #Hc⟩
  ihave %Hγ := watcherMeta_agree _ _ _ _ $$ Hm Hm'
  subst Hγ
  ihave %Hfx := watcherFixed_agree w' r r' fcs fcs' $$ [$Hf $Hf']
  obtain ⟨rfl, rfl⟩ := Hfx
  ihave %HDfs : ⌜∀ dl ∈ D, dl.2 = filtered fs0 dl.1⌝ $$ []
  · iapply pure_forall.2; iintro %dl
    iapply pure_forall.2; iintro %hdl
    icases HD $$ %dl %hdl with ⟨%fs, -, #Hsf', %hfs⟩
    ihave %hag := api.savedFilters_agree γw.fg fs fs0 $$ [$Hsf' $Hsf]
    ipureintro; rw [hfs, hag]
  have hsent : ((pre.filter (fun y => decide (y.w = w'))).map RespM.evs).flatten =
      filtered fs0 (D.map Prod.fst).flatten := by
    rw [Hp.1, deliv_sent_flatten fs0 D HDfs]
  iapply delivCert_mono γ.st.api (fun L c0 h hon => by rw [hsent, h hon]) $$ Hc

/-- **A covered watcher's first revision is at most the response's revision plus one** (`covFact`). -/
theorem covFact_lo (γ : WsNames) (γc : WatchChanNames) (pre : List RespM) (w' : Loc) (rev : w64)
    (γw : WatcherNames) :
    covFact (GF := GF) γ γc pre w' rev ∗ watcherMeta γ w' γw ⊢ ⌜(γw.lo : Int) ≤ sint.Z rev + 1⌝ := by
  unfold covFact
  iintro ⟨⟨%γw', %r, %fcs, %D, %L', %d, #Hm', -, -, -, -, -, %Hp⟩, #Hm⟩
  ihave %Hγ := watcherMeta_agree _ _ _ _ $$ Hm Hm'
  subst Hγ
  ipureintro; exact Hp.2.2.2.2.2

/-- **An event-less response's revision is at least every earlier event-less response's**
(`respRev`, as the stream's history records the responses). -/
theorem respRev_mono (γ : WsNames) (pre : List RespM) (x : RespM) :
    respRev (GF := GF) γ pre x ⊢ ⌜x.evs = [] → x.compactRev = W64 0 →
      ∀ y ∈ pre.map RespM.toW, y.evs = [] → sint.Z y.rev ≤ sint.Z x.rev⌝ := by
  unfold respRev
  iintro ⟨(%h | ⟨%L, -, %h⟩ | %h), -⟩
  · ipureintro; intro he; exact absurd he h
  · ipureintro
    intro _ _ y hy hye
    obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
    exact h.2 y' hy' hye
  · ipureintro; intro _ hc; exact absurd hc h.1

end cert

/-! ## A send's premises (`stepOk`), from the channel invariant -/

/-- **An own response's premises** (pure; its id its watcher's, registered in the history with its
range, filters' name and first revision): its fact true, its registry info the stream's (the
registration, `replay_reg`); no coverage, no cancelled ids. -/
theorem stepOk_own (dec : GName → List (EvM → Bool)) (l : List api.sent.SEv)
    (hwf : api.sent.LogWF dec l) (rr : api.WResp) (fg : GName) (rg : WatchRange) (lo : Nat)
    (L : Log) (c0 : Int) (hreg : api.sent.SEv.reg rg.id rg fg lo ∈ l) (hid : rr.id = rg.id)
    (hneg : rg.id ≠ W64 (-1))
    (hf : api.sent.SentFact.holds (api.sent.sendsOf l) ⟨rr, rg, dec fg, lo, L, c0, [], []⟩) :
    api.sent.stepOk dec (api.sent.replay dec l) (.send rr fg rg lo L c0 [] []) := by
  refine ⟨?_, ⟨fun _ => ?_, fun h => absurd (hid ▸ h) hneg⟩, fun _ h => by
    simp [api.sent.sendFact] at h,
    fun h => absurd (hid ▸ h) hneg⟩
  · rw [← api.sent.sendsOf_eq]; exact hf
  · show api.sent.regAgree _ rr.id rg (dec fg) lo
    rw [hid]; exact api.sent.replay_reg dec l hwf _ _ _ _ hreg

/-- **A stream-wide (`-1`) response's premises** (pure): its fact true; each covered watcher
registered in the history with its recorded info; every registration of the history covered or its
id cancelled (the cancelled ids recorded: the replay's cancelled set). -/
theorem stepOk_all (dec : GName → List (EvM → Bool)) (l : List api.sent.SEv)
    (hwf : api.sent.LogWF dec l) (rr : api.WResp) (fg : GName) (rg : WatchRange) (lo : Nat)
    (L : Log) (c0 : Int) (cov : List api.sent.CovRec) (hid : rr.id = W64 (-1))
    (hcov : ∀ c ∈ cov, api.sent.SEv.reg c.1 c.2.1 c.2.2.1 c.2.2.2 ∈ l)
    (hst : ∀ id rg fg lo, api.sent.SEv.reg id rg fg lo ∈ l →
      (∃ c ∈ cov, c.1 = id) ∨ id ∈ (api.sent.replay dec l).D)
    (hf : api.sent.SentFact.holds (api.sent.sendsOf l)
      (api.sent.sendFact dec rr fg rg lo L c0 cov (api.sent.replay dec l).D)) :
    api.sent.stepOk dec (api.sent.replay dec l)
      (.send rr fg rg lo L c0 cov (api.sent.replay dec l).D) := by
  refine ⟨?_, ⟨fun h => absurd hid h, fun _ c hc => ?_⟩, fun id h => h, fun _ id w hw _ => ?_⟩
  · rw [← api.sent.sendsOf_eq]; exact hf
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    exact api.sent.replay_reg dec l hwf _ _ _ _ (hcov c' hc')
  · obtain ⟨rg', fg', lo', hm⟩ := api.sent.replay_ws_reg dec l id w hw
    rcases hst id rg' fg' lo' hm with ⟨c, hc, rfl⟩ | hd
    · exact Or.inl ⟨_, List.mem_map_of_mem hc, rfl⟩
    · exact Or.inr hd

section step
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The history's well-formedness, from the invariant's part. -/
theorem chanApiAt_wf (ι : api.WsAbs) (l : List api.sent.SEv) (dec : GName → List (EvM → Bool))
    (recv : List api.WResp) :
    api.chanApiAt (GF := GF) ι l dec recv ⊢ api.chanApiAt ι l dec recv ∗ ⌜api.sent.LogWF dec l⌝ := by
  iintro H
  icases api.chanApiAt_tok ι l dec recv $$ H with ⟨H, #Ht⟩
  iunfold api.logTok at Ht
  icases Ht with ⟨-, %hw, -⟩
  iframe H; ipureintro; exact hw

/-- The saved filters of names of the history, decoded by the invariant's decoding. -/
theorem sepL_of_get (Φ : GName → IProp GF) [∀ x, Persistent (Φ x)] (A : List GName) :
    ∀ B : List GName, (∀ x ∈ B, x ∈ A) → (□ ∀ x, ⌜x ∈ A⌝ -∗ Φ x) ⊢ [∗list] x ∈ B, Φ x
  | [], _ => by iintro -; iapply BigSepL.bigSepL_nil.2; itrivial
  | b :: B, h => by
    iintro #G
    iapply BigSepL.bigSepL_cons.2
    isplitl
    · iapply G $$ %b %(h b (List.mem_cons_self ..))
    · iapply sepL_of_get Φ A B (fun x hx => h x (List.mem_cons_of_mem _ hx)) $$ G

theorem chanApiAt_fgs (ι : api.WsAbs) (l : List api.sent.SEv) (dec : GName → List (EvM → Bool))
    (recv : List api.WResp) (fgs : List GName) (h : ∀ fg ∈ fgs, fg ∈ api.sent.fgsOf l) :
    api.chanApiAt (GF := GF) ι l dec recv ⊢
      api.chanApiAt ι l dec recv ∗ [∗list] fg ∈ fgs, api.savedFilters fg (dec fg) := by
  iintro H
  iunfold api.chanApiAt at H
  icases H with ⟨Ha, %hw, #Hf, #He, Hr, #Hn⟩
  ihave #G := api.sepL_get (fun x => api.savedFilters (GF := GF) x (dec x)) (api.sent.fgsOf l) $$ Hf
  isplitl [Ha Hr]
  · iunfold api.chanApiAt; iframe Ha Hr Hf He Hn; ipureintro; exact hw
  iapply sepL_of_get (fun x => api.savedFilters (GF := GF) x (dec x)) _ fgs h $$ G

/-- **A watcher registered on the channel is in the history** (its `chanRegW`): its registration,
and its filters' saved predicates the invariant's decoding. -/
theorem chanRegW_in (γ : WsNames) (ch : Loc) (γc : WatchChanNames) (l : List api.sent.SEv)
    (dec : GName → List (EvM → Bool)) (recv : List api.WResp) (w : Loc) (γw : WatcherNames)
    (r : WatchRange) (fcs : GoSlice) :
    api.chanApiAt (GF := GF) (wsAbsOf γ ch γc) l dec recv ∗ chanRegW γ γc w ∗ watcherMeta γ w γw ∗
      watcherFixed w r fcs ⊢
      api.chanApiAt (wsAbsOf γ ch γc) l dec recv ∗ ⌜api.sent.SEv.reg r.id r γw.fg γw.lo ∈ l⌝ ∗
        api.savedFilters γw.fg (dec γw.fg) := by
  iintro ⟨H, #Hw, #Hm, #Hf⟩
  iunfold chanRegW at Hw
  icases Hw with ⟨%γw', %r', %fcs', #Hm', #Hf', #Ht⟩
  iunfold chanRegTok at Ht
  icases Ht with ⟨%l', #Hlb, %hm⟩
  ihave %Hγ := watcherMeta_agree _ _ _ _ $$ Hm Hm'
  subst Hγ
  ihave %Hfx := watcherFixed_agree w r r' fcs fcs' $$ [$Hf $Hf']
  obtain ⟨rfl, rfl⟩ := Hfx
  iunfold api.chanApiAt at H
  icases H with ⟨Ha, %hw, #Hfs, #He, Hr, #Hn⟩
  ihave %hp := mono_list_auth_lb_valid (wsAbsOf γ ch γc).ev 1 l l' $$ Ha Hlb
  have hml : api.sent.SEv.reg r.id r γw.fg γw.lo ∈ l := by
    obtain ⟨t, ht⟩ := hp.2; rw [← ht]; exact List.mem_append_left _ hm
  ihave #G := api.sepL_get (fun x => api.savedFilters (GF := GF) x (dec x)) (api.sent.fgsOf l) $$ Hfs
  have hfg : γw.fg ∈ api.sent.fgsOf l := by
    simp only [api.sent.fgsOf, List.mem_flatMap]; exact ⟨_, hml, by simp [api.sent.SEv.fgs]⟩
  ihave #Hs := G $$ %γw.fg %hfg
  isplitl [Ha Hr]
  · iunfold api.chanApiAt; iframe Ha Hr Hfs He Hn; ipureintro; exact hw
  iframe Hs; ipureintro; exact hml

/-- **A watcher's own sent events, as the client receives them by its id** (at the sent list
`sent'`, the channel's after the send): its registration in the history, its filters' saved
predicates the decoding's, its id not `-1`; its received events positive; and their certificate
(`chanWatcher_cert`), by id. -/
theorem own_cert (γ : WsNames) (ch : Loc) (γc : WatchChanNames) (closed : Bool)
    (sent' : List RespM) (L : List Loc) (l : List api.sent.SEv) (dec : GName → List (EvM → Bool))
    (recv : List api.WResp) (w : Loc) (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice)
    (fs : List (EvM → Bool)) (hw : w ∈ L) (hL : ∀ y ∈ sent', y.w ∈ L) :
    api.chanApiAt (GF := GF) (wsAbsOf γ ch γc) l dec recv ∗
      ([∗list] w' ∈ L, chanWatcher γ γc closed sent' w') ∗
      □ ([∗list] y ∈ sent', respOk y) ∗ □ ([∗list] w' ∈ L, chanRegFact γc w') ∗
      □ ([∗list] w' ∈ L, chanRegW γ γc w') ∗ watcherMeta γ w γw ∗ watcherFixed w r fcs ∗
      api.savedFilters γw.fg fs ⊢
      api.chanApiAt (wsAbsOf γ ch γc) l dec recv ∗
      ([∗list] w' ∈ L, chanWatcher γ γc closed sent' w') ∗
      ⌜api.sent.SEv.reg r.id r γw.fg γw.lo ∈ l ∧ dec γw.fg = fs ∧ r.id ≠ W64 (-1) ∧
        api.recvEvs (sent'.map RespM.toW) r.id =
          ((sent'.filter (fun x => decide (x.w = w))).map RespM.evs).flatten ∧
        ∀ ev ∈ ((sent'.filter (fun x => decide (x.w = w))).map RespM.evs).flatten, evPos ev⌝ ∗
      delivCert γ.st.api (fun L c0 => api.onceUpTo L γw.lo c0 → ∃ hi, hi ≤ L.length ∧
        ((sent'.filter (fun x => decide (x.w = w))).map RespM.evs).flatten =
          filtered fs (watchEvents L r γw.lo hi)) := by
  iintro ⟨Ha, Hws, #Hok, #Hrf, #Hrt, #Hm, #Hf, #Hsf⟩
  icases BigSepL.bigSepL_mem_acc hw $$ Hrt with ⟨#Hrw, -⟩
  icases chanRegW_in γ ch γc l dec recv w γw r fcs $$ [$Ha $Hrw $Hm $Hf] with ⟨Ha, %hm, #Hsd⟩
  ihave %hdec := api.savedFilters_agree γw.fg (dec γw.fg) fs $$ [$Hsd $Hsf]
  ihave %hrid : ⌜r.id ≠ W64 (-1)⌝ $$ []
  · icases BigSepL.bigSepL_mem_acc hw $$ Hrf with ⟨Hrx, -⟩
    iunfold chanRegFact at Hrx
    icases Hrx with ⟨%rr, %fcs', #Hf', -, %Hrr⟩
    ihave %Hag := watcherFixed_agree w r rr fcs fcs' $$ [$Hf $Hf']
    ipureintro; rw [Hag.1]; exact Hrr
  ihave %hrecv := chan_recvEvs γc sent' L w r fcs hL hw hrid $$ [$Hok $Hrf $Hf]
  icases BigSepL.bigSepL_mem_acc hw $$ Hws with ⟨Hcw, Hback⟩
  icases chanWatcher_cert γ γc closed sent' w γw r fcs fs $$ [$Hcw $Hm $Hf $Hsf] with
    ⟨Hcw, #Hc, %Hpos⟩
  ihave Hws := Hback $$ Hcw
  iframe Ha Hws Hc
  ipureintro; exact ⟨hm, hdec, hrid, hrecv, Hpos⟩

/-- A compaction lower bound joined to a certificate. -/
theorem delivCert_crev (a : api.AbsNames) (P : Log → Int → Prop) (c : Int) :
    api.crevAtLeast (GF := GF) a c ∗ delivCert a P ⊢ delivCert a (fun L c0 => P L c0 ∧ c ≤ c0) := by
  unfold delivCert
  iintro ⟨#Hc, %L', %c', #Hn, #Hc', %hP⟩
  iexists L', max c c'
  iframe Hn
  isplitl
  · by_cases h : c ≤ c'
    · rw [Int.max_eq_right h]; iexact Hc'
    · rw [Int.max_eq_left (by omega)]; iright; iexact Hc
  · ipureintro
    intro L c0 hL hc
    exact ⟨hP L c0 hL (by omega), by omega⟩

/-- **The covered watchers' certificates** (a `-1` response's, `cs` its covered watchers, each one
of the channel's: its entry, its coverage before the response, its registration on the channel
and in the history): each covered watcher's events received by its id up to the response's
revision, joined to a certificate `Q`; and each one registered in the history with its names'
info. -/
theorem cov_certs (γ : WsNames) (ch : Loc) (γc : WatchChanNames) (sent : List RespM)
    (L : List Loc) (l : List api.sent.SEv) (dec : GName → List (EvM → Bool))
    (recv : List api.WResp) (rev : w64) (hrev : 0 ≤ sint.Z rev) (hL : ∀ y ∈ sent, y.w ∈ L)
    (Q : Log → Int → Prop) :
    ∀ cs : List CovArg,
    api.chanApiAt (GF := GF) (wsAbsOf γ ch γc) l dec recv ∗ delivCert γ.st.api Q ∗
      □ ([∗list] y ∈ sent, respOk y) ∗ □ ([∗list] w' ∈ L, chanRegFact γc w') ∗
      □ (∀ c : CovArg, ⌜c ∈ cs⌝ -∗ ⌜c.w ∈ L⌝ ∗ covEntry γ γc rev c ∗ covFact γ γc sent c.w rev ∗
        chanRegW γ γc c.w) ⊢
      api.chanApiAt (wsAbsOf γ ch γc) l dec recv ∗
      ⌜∀ c ∈ cs, api.sent.SEv.reg c.r.id c.r c.γw.fg c.γw.lo ∈ l⌝ ∗
      delivCert γ.st.api (fun L c0 => Q L c0 ∧ ∀ c ∈ cs, api.onceUpTo L c.γw.lo c0 →
        api.recvEvs (sent.map RespM.toW) c.r.id =
          filtered (dec c.γw.fg) (watchEvents L c.r c.γw.lo (sint.nat rev + 1)))
  | [] => by
    iintro ⟨Ha, #Hq, -⟩
    iframe Ha
    isplitr
    · ipureintro; intro c hc; cases hc
    iapply delivCert_mono _ (fun L c h => ⟨h, fun c hc => by cases hc⟩) $$ Hq
  | c :: cs => by
    iintro ⟨Ha, #Hq, #Hok, #Hrf, #Hcs⟩
    icases Hcs $$ %c %(List.mem_cons_self ..) with ⟨%hcL, #Hce, #Hcf, #Hrw⟩
    iunfold covEntry at Hce
    icases Hce with ⟨#Hm, -, #Hf, -⟩
    icases chanRegW_in γ ch γc l dec recv c.w c.γw c.r c.fcs $$ [$Ha $Hrw $Hm $Hf] with
      ⟨Ha, %hm, #Hsd⟩
    ihave %hrid : ⌜c.r.id ≠ W64 (-1)⌝ $$ []
    · icases BigSepL.bigSepL_mem_acc hcL $$ Hrf with ⟨Hrx, -⟩
      iunfold chanRegFact at Hrx
      icases Hrx with ⟨%rr, %fcs', #Hf', -, %Hrr⟩
      ihave %Hag := watcherFixed_agree c.w c.r rr c.fcs fcs' $$ [$Hf $Hf']
      ipureintro; rw [Hag.1]; exact Hrr
    ihave %hrecv := chan_recvEvs γc sent L c.w c.r c.fcs hL hcL hrid $$ [$Hok $Hrf $Hf]
    ihave #Hc1 := covFact_recv γ γc sent c.w rev hrev c.γw c.r c.fcs (dec c.γw.fg) $$
      [$Hcf $Hm $Hf $Hsd]
    ihave #Hcs' : □ (∀ c' : CovArg, ⌜c' ∈ cs⌝ -∗ ⌜c'.w ∈ L⌝ ∗ covEntry γ γc rev c' ∗
        covFact γ γc sent c'.w rev ∗ chanRegW γ γc c'.w) $$ []
    · iintro !> %c' %hc'
      iapply Hcs $$ %c' %(List.mem_cons_of_mem _ hc')
    icases cov_certs γ ch γc sent L l dec recv rev hrev hL Q cs $$ [$Ha $Hq $Hok $Hrf $Hcs'] with
      ⟨Ha, %hms, #Hc2⟩
    ihave #Hj := delivCert_join γ.st.api
      (fun L c0 => api.onceUpTo L c.γw.lo c0 →
        ((sent.filter (fun y => decide (y.w = c.w))).map RespM.evs).flatten =
          filtered (dec c.γw.fg) (watchEvents L c.r c.γw.lo (sint.nat rev + 1)))
      (fun L c0 => Q L c0 ∧ ∀ c ∈ cs, api.onceUpTo L c.γw.lo c0 →
        api.recvEvs (sent.map RespM.toW) c.r.id =
          filtered (dec c.γw.fg) (watchEvents L c.r c.γw.lo (sint.nat rev + 1))) $$ [$Hc1 $Hc2]
    iframe Ha
    isplitr
    · ipureintro
      intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | h
      · exact hm
      · exact hms c' h
    iapply delivCert_mono _ (fun L c0 h => ⟨h.2.1, fun c' hc' hon => by
      rcases List.mem_cons.1 hc' with rfl | h'
      · rw [hrecv]; exact h.1 hon
      · exact h.2.2 c' h' hon⟩) $$ Hj

/-- The covered watchers are registered on the channel. -/
theorem covPre_mem (γ : WsNames) (γc : WatchChanNames) (rev : w64) (L : List Loc)
    (cs : List CovArg) :
    ghostMapAuth (GF := GF) γc.reg 1 (regMap L) ∗ covPre γ γc rev cs ⊢ ⌜∀ c ∈ cs, c.w ∈ L⌝ := by
  iintro ⟨Ha, #H⟩
  iapply pure_forall.2; iintro %c
  iapply pure_forall.2; iintro %hc
  iunfold covPre at H
  icases BigSepL.bigSepL_mem_acc hc $$ H with ⟨Hc, -⟩
  iunfold covEntry at Hc
  icases Hc with ⟨-, -, -, -, -, -, #He⟩
  ihave %Hl := ghost_map_lookup $$ Ha He
  ipureintro
  exact (regMap_lookup L c.w).1 (by rw [show regMap L !! c.w = (regMap L).lookup c.w from rfl, Hl]; rfl)

/-- **A `-1` response's stamps** (`stampsAt`): every registration of the history is a watcher of the
channel (`regWit`), so registered when the response is sent: covered by it (one of `cs`, by its
range's id), or cancelled (`rsnW`: its id in the replay's cancelled set). -/
theorem stamps_of (γ : WsNames) (ch : Loc) (γc : WatchChanNames) (l : List api.sent.SEv)
    (dec : GName → List (EvM → Bool)) (recv : List api.WResp) (L : List Loc) (cs : List CovArg)
    (rev : w64) :
    api.chanApiAt (GF := GF) (wsAbsOf γ ch γc) l dec recv ∗ ghostMapAuth γc.reg 1 (regMap L) ∗
      regWit γc l ∗ (□ ∀ w : Loc, ⌜w ∈ L⌝ -∗ ⌜w ∈ cs.map CovArg.w⌝ ∨ rsnW γc w) ∗
      covPre γ γc rev cs ⊢
      ⌜∀ id rg fg lo, api.sent.SEv.reg id rg fg lo ∈ l →
        (∃ c ∈ cs, c.r.id = id) ∨ id ∈ (api.sent.replay dec l).D⌝ := by
  iintro ⟨Ha, Hreg, #Hwit, #Hall, #Hcp⟩
  iapply pure_forall.2; iintro %id
  iapply pure_forall.2; iintro %rg
  iapply pure_forall.2; iintro %fg
  iapply pure_forall.2; iintro %lo
  iapply pure_forall.2; iintro %hm
  iunfold regWit at Hwit
  icases Hwit $$ %id %rg %fg %lo %hm with ⟨%wl, %fcs, #Hrw, #Hf, %hid⟩
  ihave %Hl := ghost_map_lookup $$ Hreg Hrw
  have hwl : wl ∈ L :=
    (regMap_lookup L wl).1 (by rw [show regMap L !! wl = (regMap L).lookup wl from rfl, Hl]; rfl)
  icases Hall $$ %wl %hwl with (%hc | #Hr)
  · obtain ⟨c, hc2, rfl⟩ := List.mem_map.1 hc
    iunfold covPre at Hcp
    icases BigSepL.bigSepL_mem_acc hc2 $$ Hcp with ⟨Hce, -⟩
    iunfold covEntry at Hce
    icases Hce with ⟨-, -, #Hf', -⟩
    ihave %Hag := watcherFixed_agree c.w rg c.r fcs c.fcs $$ [$Hf $Hf']
    ipureintro; left; exact ⟨c, hc2, by rw [hid, Hag.1]⟩
  · iunfold rsnW at Hr
    icases Hr with ⟨%r', %fcs', #Hf', #Hct⟩
    ihave %Hag := watcherFixed_agree wl rg r' fcs fcs' $$ [$Hf $Hf']
    ihave #Hct' : api.cancelTok (wsAbsOf γ ch γc) id $$ []
    · rw [hid, Hag.1]; iunfold chanCancelTok at Hct; iunfold api.cancelTok; iexact Hct
    icases api.chanApiAt_dead _ l dec recv id $$ [$Ha $Hct'] with ⟨-, %hd⟩
    ipureintro; right; exact hd

/-- A lent notified log is not empty. -/
theorem notifiedLent_ne (γ : WsNames) (nl : Option (Qp × Log)) :
    notifiedLent (GF := GF) γ nl ⊢ ⌜∀ q L, nl = some (q, L) → L ≠ []⌝ := by
  cases nl with
  | none => iintro -; ipureintro; intro q L h; cases h
  | some p =>
    obtain ⟨q, L⟩ := p
    unfold notifiedLent
    iintro ⟨-, %h⟩
    ipureintro; intro q' L' he; cases he; exact h

/-- A compaction lower bound, `-1` (none) minted. -/
theorem crevAtLeast_of (a : api.AbsNames) (c0 : Int) :
    (⌜c0 = -1⌝ ∨ api.crevAtLeast (GF := GF) a c0) ⊢ |==> api.crevAtLeast a c0 := by
  iintro (%h | #H)
  · subst h
    unfold api.crevAtLeast
    rw [show api.crevN (-1) = 0 from rfl]
    imod (monoNatLbOwn_0 (GF := GF) a.crevLb) with #H0
    imodintro; iexact H0
  · imodintro; iexact H

/-- **A send's step of the stream's history**: its event (`.send`) appended with its premises, the
channel's sent list gaining the response. -/
theorem chanApi_finish (γ : WsNames) (ch : Loc) (γc : WatchChanNames) (sent : List RespM)
    (recv : List RespM) (x : RespM) (l : List api.sent.SEv) (dec : GName → List (EvM → Bool))
    (fg : GName) (rg : WatchRange) (lo : Nat) (NL : Log) (c0 : Int) (cov : List api.sent.CovRec)
    (dead : List w64) (hsl : api.sent.sendsOf l = sent.map RespM.toW)
    (hok : api.sent.stepOk dec (api.sent.replay dec l) (.send x.toW fg rg lo NL c0 cov dead))
    (hfgs : ∀ g ∈ (api.sent.SEv.send x.toW fg rg lo NL c0 cov dead).fgs, g ∈ api.sent.fgsOf l) :
    api.chanApiAt (GF := GF) (wsAbsOf γ ch γc) l dec (recv.map RespM.toW) ∗ regWit γc l ∗
      api.nlLb γ.st.api NL ∗ (⌜c0 = -1⌝ ∨ api.crevAtLeast γ.st.api c0) ==∗
      chanApi γ ch γc (sent ++ [x]) recv := by
  iintro ⟨Ha, #Hwit, #Hn, Hc⟩
  imod crevAtLeast_of γ.st.api c0 $$ Hc with #Hc
  icases chanApiAt_fgs _ l dec _ _ hfgs $$ Ha with ⟨Ha, #Hf⟩
  ihave #Hev : api.evTok (wsAbsOf γ ch γc).st (.send x.toW fg rg lo NL c0 cov dead) $$ []
  · iunfold api.evTok; isplitl; iexact Hn; iexact Hc
  imod api.chanApiAt_send _ l dec _ _ rfl hok $$ [$Ha $Hf $Hev] with Ha
  imodintro
  iunfold chanApi
  iexists l ++ [.send x.toW fg rg lo NL c0 cov dead], dec
  iframe Ha
  isplitr
  · ipureintro; rw [api.sent.sendsOf_append, hsl]; simp [api.sent.sendsOf]
  · iapply regWit_app γc l _ (fun _ _ _ _ h => by cases h) $$ Hwit

/-- **A response's send on the stream's history** (`watcher.send`'s, its compaction revision `0`;
the channel invariant open, after `entries_deliver`, the watchers' entries at the sent list with
the response): the response's event appended, its premises (`stepOk`) assembled from the
certificates (`WatchSendApi`'s) and `SentInv`'s `holds_*`: its watcher's own response (id `r.id`),
or a stream-wide progress response (id `-1`, covering the watchers `cs`). -/
theorem chanApi_send_resp (γ : WsNames) (ch : Loc) (γc : WatchChanNames) (closed : Bool)
    (sent recv : List RespM) (L : List Loc) (x : RespM) (cs : List CovArg) (w : Loc) (rev : w64)
    (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice) (fs : List (EvM → Bool))
    (hxw : x.w = w) (hxr : x.rev = rev) (hw : x.w ∈ L) (hL : ∀ y ∈ sent ++ [x], y.w ∈ L)
    (hcov : x.cov = cs.map CovArg.w) (hregs : x.regs = L)
    (hid : x.id = r.id ∨ x.id = W64 (-1)) (hc : x.compactRev = W64 0)
    (hrev0 : x.evs = [] → 0 ≤ sint.Z x.rev)
    (hle : ∀ ev ∈ x.evs, sint.Z ev.kv.modRev ≤ sint.Z x.rev) :
    chanApi (GF := GF) γ ch γc sent recv ∗
      ([∗list] w' ∈ L, chanWatcher γ γc closed (sent ++ [x]) w') ∗
      ghostMapAuth γc.reg 1 (regMap L) ∗
      □ ([∗list] y ∈ sent ++ [x], respOk y) ∗ □ ([∗list] w' ∈ L, chanRegFact γc w') ∗
      □ ([∗list] w' ∈ L, chanRegW γ γc w') ∗ watcherMeta γ w γw ∗ watcherFixed w r fcs ∗
      api.savedFilters γw.fg fs ∗ respCov γ γc sent x ∗ covPre γ γc rev cs ==∗
      chanApi γ ch γc (sent ++ [x]) recv ∗
      ([∗list] w' ∈ L, chanWatcher γ γc closed (sent ++ [x]) w') ∗
      ghostMapAuth γc.reg 1 (regMap L) := by
  subst hxw hxr
  iintro ⟨Hapi, Hws, Hreg, #Hok, #Hrf, #Hrt, #Hm, #Hf, #Hsf, #Hrc, #Hcp⟩
  iunfold chanApi at Hapi
  icases Hapi with ⟨%l, %dec, Ha, %Hsl, #Hwit⟩
  icases chanApiAt_wf _ l dec _ $$ Ha with ⟨Ha, %Hwf⟩
  icases own_cert γ ch γc closed (sent ++ [x]) L l dec (recv.map RespM.toW) x.w γw r fcs fs hw hL
    $$ [$Ha $Hws $Hok $Hrf $Hrt $Hm $Hf $Hsf] with ⟨Ha, Hws, %Hown, #Hcd⟩
  obtain ⟨hmw, hdec, hrid, hrecv', hpos⟩ := Hown
  iunfold respCov at Hrc
  icases Hrc with ⟨#Hcf, #Hcompl, %Hself, #Hrr⟩
  ihave %hmono := respRev_mono γ sent x $$ Hrr
  iunfold respRev at Hrr
  icases Hrr with ⟨-, -, (%hcne | #Hra)⟩
  · exact absurd hc hcne
  ihave #Hcr := revApi_cert γ x.rev $$ Hra
  have hfw : ∀ g ∈ [γw.fg], g ∈ api.sent.fgsOf l := by
    intro g hg
    rw [List.mem_singleton] at hg; subst hg
    simp only [api.sent.fgsOf, List.mem_flatMap]; exact ⟨_, hmw, by simp [api.sent.SEv.fgs]⟩
  have hsplit : ((sent ++ [x]).filter (fun y => decide (y.w = x.w))).map RespM.evs =
      (sent.filter (fun y => decide (y.w = x.w))).map RespM.evs ++ [x.evs] := by
    simp [List.filter_append]
  rcases hid with hid | hid
  · -- its watcher's own response
    ihave #Hcp' : delivCert γ.st.api (fun L c0 => x.evs = [] → api.onceUpTo L γw.lo c0 →
        ((sent.filter (fun y => decide (y.w = x.w))).map RespM.evs).flatten =
          filtered fs (watchEvents L r γw.lo (sint.nat x.rev + 1))) $$ []
    · by_cases he : x.evs = []
      · ihave #Hcw := Hcf $$ %x.w %(Hself he hc)
        ihave #C := covFact_recv γ γc sent x.w x.rev (hrev0 he) γw r fcs fs $$ [$Hcw $Hm $Hf $Hsf]
        iapply delivCert_mono _ (fun L c0 h _ => h) $$ C
      · iapply delivCert_mono _ (fun L c0 _ h => absurd h he) $$ Hcr
    ihave %hlo : ⌜x.evs = [] → (γw.lo : Int) ≤ sint.Z x.rev + 1⌝ $$ []
    · by_cases he : x.evs = []
      · ihave #Hcw := Hcf $$ %x.w %(Hself he hc)
        ihave %h := covFact_lo γ γc sent x.w x.rev γw $$ [$Hcw $Hm]
        ipureintro; exact fun _ => h
      · ipureintro; exact fun h => absurd h he
    ihave #J := delivCert_join γ.st.api (fun L _ => sint.nat x.rev < L.length)
      (fun L c0 => api.onceUpTo L γw.lo c0 → ∃ hi, hi ≤ L.length ∧
        (((sent ++ [x]).filter (fun y => decide (y.w = x.w))).map RespM.evs).flatten =
          filtered fs (watchEvents L r γw.lo hi)) $$ [$Hcr $Hcd]
    ihave #J2 := delivCert_join γ.st.api _
      (fun L c0 => x.evs = [] → api.onceUpTo L γw.lo c0 →
        ((sent.filter (fun y => decide (y.w = x.w))).map RespM.evs).flatten =
          filtered fs (watchEvents L r γw.lo (sint.nat x.rev + 1))) $$ [$J $Hcp']
    icases delivCert_elim γ.st.api _ $$ J2 with ⟨%NL, %c0, #Hn, Hc0, %HP⟩
    obtain ⟨⟨hrevL, hdel⟩, hprog⟩ := HP
    have hxid : x.toW.id = r.id := hid
    have hok : api.sent.stepOk dec (api.sent.replay dec l)
        (.send x.toW γw.fg r γw.lo NL c0 [] []) := by
      refine stepOk_own dec l Hwf x.toW γw.fg r γw.lo NL c0 hmw hxid hrid ?_
      rw [Hsl, hdec]
      refine holds_own _ x.toW r fs γw.lo NL c0 [] (hxid ▸ hrid) hc hle hrevL
        (fun ev hev => hpos ev ?_) (fun hon => ?_) (fun he hon => ?_) hlo
        (fun he => hmono he hc)
      · rw [hsplit]; simp only [List.flatten_append, List.flatten_singleton]
        exact List.mem_append_right _ hev
      · obtain ⟨hi, hhi, heq⟩ := hdel hon
        refine ⟨hi, hhi, ?_⟩
        rw [hxid, show sent.map RespM.toW ++ [x.toW] = (sent ++ [x]).map RespM.toW by simp, hrecv', heq]
      · have h1 := hrecv'
        rw [List.map_append, List.map_singleton, api.sent.recvEvs_snoc, if_pos hxid, hsplit,
          List.flatten_append, List.flatten_singleton] at h1
        have he' : x.evs = [] := he
        rw [hxid, api.sent.recvEvs_snoc, if_pos hxid]
        rw [show x.toW.evs = x.evs from rfl, he', List.append_nil] at h1 ⊢
        rw [List.append_nil] at h1
        rw [h1]
        exact hprog he' hon
    imod chanApi_finish γ ch γc sent recv x l dec γw.fg r γw.lo NL c0 [] [] Hsl hok
      (by simpa [api.sent.SEv.fgs] using hfw) $$ [$Ha $Hwit $Hn $Hc0] with Hapi
    imodintro
    iframe Hapi Hws Hreg
  · -- a stream-wide progress response
    iunfold respCompl at Hcompl
    icases Hcompl with (%hne | ⟨#Hall, %Hr1⟩)
    · exact absurd hid hne
    obtain ⟨h1, hevs⟩ := Hr1
    ihave %hcsL := covPre_mem γ γc x.rev L cs $$ [$Hreg $Hcp]
    ihave #Hcw : □ (∀ c : CovArg, ⌜c ∈ cs⌝ -∗ ⌜c.w ∈ L⌝ ∗ covEntry γ γc x.rev c ∗
        covFact γ γc sent c.w x.rev ∗ chanRegW γ γc c.w) $$ []
    · iintro !> %c %hc
      isplitr
      · ipureintro; exact hcsL c hc
      iunfold covPre at Hcp
      icases BigSepL.bigSepL_mem_acc hc $$ Hcp with ⟨Hce, -⟩
      iframe Hce
      isplitr
      · iapply Hcf $$ %c.w %(by rw [hcov]; exact List.mem_map_of_mem hc)
      · icases BigSepL.bigSepL_mem_acc (hcsL c hc) $$ Hrt with ⟨H, -⟩; iexact H
    ihave #Hok0 : □ ([∗list] y ∈ sent, respOk y) $$ []
    · iintro !>
      icases BigSepL.bigSepL_append.1 $$ Hok with ⟨H, -⟩
      iexact H
    have hL0 : ∀ y ∈ sent, y.w ∈ L := fun y hy => hL y (List.mem_append_left _ hy)
    icases cov_certs γ ch γc sent L l dec (recv.map RespM.toW) x.rev (by omega) hL0
      (fun L _ => sint.nat x.rev < L.length) cs $$ [$Ha $Hcr $Hok0 $Hrf $Hcw] with
      ⟨Ha, %hms, #Hcc⟩
    ihave #Hall' : □ (∀ w : Loc, ⌜w ∈ L⌝ -∗ ⌜w ∈ cs.map CovArg.w⌝ ∨ rsnW γc w) $$ []
    · rw [← hcov, ← hregs]; iexact Hall
    icases persistent_entails_right (stamps_of γ ch γc l dec (recv.map RespM.toW) L cs x.rev)
      $$ [$Ha $Hreg $Hwit $Hall' $Hcp] with ⟨%hst, ⟨Ha, Hreg, -⟩⟩
    icases delivCert_elim γ.st.api _ $$ Hcc with ⟨%NL, %c0, #Hn, Hc0, %HP⟩
    obtain ⟨hrevL, hcovs⟩ := HP
    ihave %hclo : ⌜∀ c ∈ cs, (c.γw.lo : Int) ≤ sint.Z x.rev + 1⌝ $$ []
    · iapply pure_forall.2; iintro %c
      iapply pure_forall.2; iintro %hc
      iunfold covPre at Hcp
      icases BigSepL.bigSepL_mem_acc hc $$ Hcp with ⟨Hce, -⟩
      iunfold covEntry at Hce
      icases Hce with ⟨-, -, -, -, -, %h, -⟩
      ipureintro; exact h.2.2
    let covR : List api.sent.CovRec := cs.map (fun c => (c.r.id, c.r, c.γw.fg, c.γw.lo))
    have hxid : x.toW.id = W64 (-1) := hid
    have hok : api.sent.stepOk dec (api.sent.replay dec l)
        (.send x.toW γw.fg r γw.lo NL c0 covR (api.sent.replay dec l).D) := by
      refine stepOk_all dec l Hwf x.toW γw.fg r γw.lo NL c0 covR hxid ?_ ?_ ?_
      · intro c hc
        obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
        exact hms c' hc'
      · intro id rg fg lo hm
        rcases hst id rg fg lo hm with ⟨c, hc, rfl⟩ | hd
        · exact Or.inl ⟨_, List.mem_map_of_mem hc, rfl⟩
        · exact Or.inr hd
      · rw [Hsl]
        refine holds_all _ x.toW NL c0 _ _ r (dec γw.fg) γw.lo hxid hevs hc h1 hrevL ?_ ?_
          (hmono hevs hc)
        rotate_left
        · intro c hc
          obtain ⟨c1, hc1, rfl⟩ := List.mem_map.1 hc
          obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc1
          exact hclo c' hc'
        intro c hc hon
        obtain ⟨c1, hc1, rfl⟩ := List.mem_map.1 hc
        obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc1
        rw [api.sent.recvEvs_snoc, show x.toW.evs = x.evs from rfl, hevs, ite_self, List.append_nil]
        exact hcovs c' hc' hon
    have hfgs : ∀ g ∈ (api.sent.SEv.send x.toW γw.fg r γw.lo NL c0 covR
        (api.sent.replay dec l).D).fgs, g ∈ api.sent.fgsOf l := by
      intro g hg
      simp only [api.sent.SEv.fgs, List.mem_cons, List.mem_map, covR] at hg
      rcases hg with rfl | ⟨c, ⟨c', hc', rfl⟩, rfl⟩
      · exact hfw _ (List.mem_singleton_self _)
      · simp only [api.sent.fgsOf, List.mem_flatMap]
        exact ⟨_, hms c' hc', by simp [api.sent.SEv.fgs]⟩
    imod chanApi_finish γ ch γc sent recv x l dec γw.fg r γw.lo NL c0 covR _ Hsl hok hfgs
      $$ [$Ha $Hwit $Hn $Hc0] with Hapi
    imodintro
    iframe Hapi Hws Hreg

/-- **A compaction response's send on the stream's history** (`chooseAll`'s, `cmp_send_inner`: its
watcher's id, no events, revision `0`, a positive compaction revision the API's at least): its
event appended, its premises assembled (`holds_cmp`). -/
theorem chanApi_send_cmp (γ : WsNames) (ch : Loc) (γc : WatchChanNames) (closed : Bool)
    (sent recv : List RespM) (L : List Loc) (x : RespM) (w : Loc) (c : w64)
    (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice) (fs : List (EvM → Bool))
    (hxw : x.w = w) (hxc : x.compactRev = c)
    (hw : x.w ∈ L) (hL : ∀ y ∈ sent ++ [x], y.w ∈ L) (hid : x.id = r.id) (he : x.evs = [])
    (hr : x.rev = W64 0) (hc1 : 0 < sint.Z x.compactRev) :
    chanApi (GF := GF) γ ch γc sent recv ∗
      ([∗list] w' ∈ L, chanWatcher γ γc closed (sent ++ [x]) w') ∗
      □ ([∗list] y ∈ sent ++ [x], respOk y) ∗ □ ([∗list] w' ∈ L, chanRegFact γc w') ∗
      □ ([∗list] w' ∈ L, chanRegW γ γc w') ∗ watcherMeta γ w γw ∗ watcherFixed w r fcs ∗
      api.savedFilters γw.fg fs ∗ api.crevAtLeast γ.st.api (sint.Z c) ==∗
      chanApi γ ch γc (sent ++ [x]) recv ∗
      ([∗list] w' ∈ L, chanWatcher γ γc closed (sent ++ [x]) w') := by
  subst hxw hxc
  iintro ⟨Hapi, Hws, #Hok, #Hrf, #Hrt, #Hm, #Hf, #Hsf, #Hcv⟩
  iunfold chanApi at Hapi
  icases Hapi with ⟨%l, %dec, Ha, %Hsl, #Hwit⟩
  icases chanApiAt_wf _ l dec _ $$ Ha with ⟨Ha, %Hwf⟩
  icases own_cert γ ch γc closed (sent ++ [x]) L l dec (recv.map RespM.toW) x.w γw r fcs fs hw hL
    $$ [$Ha $Hws $Hok $Hrf $Hrt $Hm $Hf $Hsf] with ⟨Ha, Hws, %Hown, #Hcd⟩
  obtain ⟨hmw, hdec, hrid, hrecv', -⟩ := Hown
  ihave #J := delivCert_crev γ.st.api _ _ $$ [$Hcv $Hcd]
  icases delivCert_elim γ.st.api _ $$ J with ⟨%NL, %c0, #Hn, Hc0, %HP⟩
  obtain ⟨hdel, hcle⟩ := HP
  have hxid : x.toW.id = r.id := hid
  have hcne : x.compactRev ≠ W64 0 := by intro h; rw [h] at hc1; exact absurd hc1 (by decide)
  have hok : api.sent.stepOk dec (api.sent.replay dec l) (.send x.toW γw.fg r γw.lo NL c0 [] []) := by
    refine stepOk_own dec l Hwf x.toW γw.fg r γw.lo NL c0 hmw hxid hrid ?_
    rw [Hsl, hdec]
    refine holds_cmp _ x.toW r fs γw.lo NL c0 [] (hxid ▸ hrid) hcne he hr hc1 hcle (fun hon => ?_)
    obtain ⟨hi, hhi, heq⟩ := hdel hon
    refine ⟨hi, hhi, ?_⟩
    rw [hxid, show sent.map RespM.toW ++ [x.toW] = (sent ++ [x]).map RespM.toW by simp, hrecv', heq]
  have hfgs : ∀ g ∈ (api.sent.SEv.send x.toW γw.fg r γw.lo NL c0 [] []).fgs,
      g ∈ api.sent.fgsOf l := by
    intro g hg
    simp only [api.sent.SEv.fgs, List.map_nil, List.mem_singleton] at hg; subst hg
    simp only [api.sent.fgsOf, List.mem_flatMap]; exact ⟨_, hmw, by simp [api.sent.SEv.fgs]⟩
  imod chanApi_finish γ ch γc sent recv x l dec γw.fg r γw.lo NL c0 [] [] Hsl hok hfgs
    $$ [$Ha $Hwit $Hn $Hc0] with Hapi
  imodintro
  iframe Hapi Hws

end step

end mvcc
end EtcdGrove
end Perennial
