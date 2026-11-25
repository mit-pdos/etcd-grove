/-
Lean-first (no Rocq counterpart).

# The bridge to Kubernetes' checker, B5: the driver's watch check implies `ValidateWatch` (k8s 7g step 4)

`notes/k8s-7g-scope.md` §2.3, B5. A watch the driver's check accepts (`watchOkL`, at the
configuration `h` of its linearization point) is accepted by upstream's `WatchValidator`
(`validateWatchL`) on the events `realCheck` gives it (`realEventsL`, D7g-2/3), against a replay
`R` that agrees with `h` from the seeded revision `s0` on (`ReplayAt`, B3b).

The received events are the store's `watch.Event`s (`REv`); the driver's own check reads them as
`toWEvent` maps them (`toWEvL`), encoded in the output and decoded (`decWEventsL`). The premises
beyond `watchOkL`:

- the history's facts (`HistWf`, `HistSorted`, its length the revision, `1 ≤ s0 ≤` its revision);
- the requested resource version below `2^63` (`InOk`'s; without it, `watchRangeL`'s `req + 1`
  wraps at `2^64 - 1` where the driver's natural-number range does not, and B5 is false);
- **`WatchFromL s0 x all`**: the events after the initial ones (a watch-list's from its first
  bookmark; any other watch's all of them) mark revisions after `s0`: the replay knows the changes
  from `s0` on only. The store's watch starts at or after the revision it had when the watch was
  made, after the seeds (scope R3; read off `kStreamOk`'s start in step 5).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealReplay
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatchStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open k8s_etcd3 k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts]

/-! ## The driver's glue (`watch.go`, `realcheck.go`) -/

/-- **`toWEvent(ev)`** (`watch.go`): the four object event types with a `*Obj` its record and type
(`WAdded` 0, `WModified` 1, `WDeleted` 2, `WBookmark` 3), an Error with a `*metav1.Status` of status
`Failure` a `WError` (4), anything else `WBad` (5); the zero object but for the first. -/
def toWEvL (e : REv) : WEv :=
  if e.ty = evAdded ∨ e.ty = evModified ∨ e.ty = evDeleted ∨ e.ty = evBookmark then
    match e.o with
    | .obj o =>
      ⟨if e.ty = evModified then 1 else if e.ty = evDeleted then 2
        else if e.ty = evBookmark then 3 else 0, o⟩
    | _ => ⟨5, zObj⟩
  else if e.ty = evError then
    match e.o with
    | .status s => if s = go!"Failure" then ⟨4, zObj⟩ else ⟨5, zObj⟩
    | _ => ⟨5, zObj⟩
  else ⟨5, zObj⟩

/-- **`realEvents(in, evs)`** (`realcheck.go`): cut after the first Error event (D7g-2); for a
watch-list, nothing if no bookmark is left (D7g-3). -/
def realEventsL (x : Input) (evs : List REv) : List REv :=
  let cut := match evs.findIdx? (fun e => decide (e.ty = evError)) with
    | some i => evs.take (i + 1)
    | none => evs
  if x.SendInit' = W64 2 then
    (if cut.any (fun e => decide (e.ty = evBookmark)) then cut else [])
  else cut

/-! ## The premise on where a watch starts -/

/-- **The events after the initial ones mark revisions after `s0`** (`evLo`: an event's own
revision, a bookmark's plus one): for a watch-list, the non-error events from the first bookmark
on; for any other watch, all its non-error events. -/
def WatchFromL (s0 : w64) (x : Input) (all : List WEv) : Prop :=
  ∀ e ∈ (if x.SendInit' = W64 2 then (nonErr all).dropWhile (fun e => e.t ≠ 3) else nonErr all),
    uint.nat s0 < evLo e

/-! ## Facts for B5 -/

/-- The received event a driver's event stands for: the inverse of `toWEvL` on types below 5. -/
def fromW (e : WEv) : REv :=
  if e.t = 0 then ⟨evAdded, .obj e.o⟩
  else if e.t = 1 then ⟨evModified, .obj e.o⟩
  else if e.t = 2 then ⟨evDeleted, .obj e.o⟩
  else if e.t = 3 then ⟨evBookmark, .obj e.o⟩
  else if e.t = 4 then ⟨evError, .status go!"Failure"⟩
  else ⟨[], .other⟩

theorem fromW_toWEvL (e : REv) (h : (toWEvL e).t < 5) : fromW (toWEvL e) = e := by
  obtain ⟨ty, o⟩ := e
  unfold toWEvL at h ⊢
  simp only at h ⊢
  by_cases h1 : ty = evAdded ∨ ty = evModified ∨ ty = evDeleted ∨ ty = evBookmark
  · rw [if_pos h1] at h ⊢
    cases o with
    | obj o =>
      simp only at h ⊢
      rcases h1 with rfl | rfl | rfl | rfl <;> simp [fromW, evAdded, evModified, evDeleted, evBookmark]
    | status s => simp at h
    | other => simp at h
  · rw [if_neg h1] at h ⊢
    by_cases h2 : ty = evError
    · subst h2
      rw [if_pos rfl] at h ⊢
      cases o with
      | obj o => simp at h
      | status s =>
        simp only at h ⊢
        by_cases hs : s = go!"Failure"
        · subst hs; simp [fromW]
        · simp [hs] at h
      | other => simp at h
    · rw [if_neg h2] at h; simp at h

theorem fromW_ty_err (e : WEv) : (fromW e).ty = evError ↔ e.t = 4 := by
  unfold fromW
  by_cases h0 : e.t = 0 <;> by_cases h1 : e.t = 1 <;> by_cases h2 : e.t = 2 <;>
    by_cases h3 : e.t = 3 <;> by_cases h4 : e.t = 4 <;>
    simp_all [evAdded, evModified, evDeleted, evBookmark, evError]

theorem fromW_ty_bm (e : WEv) : (fromW e).ty = evBookmark ↔ e.t = 3 := by
  unfold fromW
  by_cases h0 : e.t = 0 <;> by_cases h1 : e.t = 1 <;> by_cases h2 : e.t = 2 <;>
    by_cases h3 : e.t = 3 <;> by_cases h4 : e.t = 4 <;>
    simp_all [evAdded, evModified, evDeleted, evBookmark, evError]

/-- An object event (types 0 to 3) stands for an event of the same object. -/
theorem fromW_obj (e : WEv) (h : e.t ≤ 3) : (fromW e).o = .obj e.o := by
  unfold fromW
  by_cases h0 : e.t = 0 <;> by_cases h1 : e.t = 1 <;> by_cases h2 : e.t = 2 <;>
    by_cases h3 : e.t = 3 <;> simp_all <;> omega

theorem fromW_err (e : WEv) (h : e.t = 4) : fromW e = ⟨evError, .status go!"Failure"⟩ := by
  simp [fromW, h]

/-- `realEvents`' cut after the first Error event (D7g-2), on the driver's events. -/
def cut0 (W : List WEv) : List WEv :=
  match W.findIdx? (fun e => decide (e.t = 4)) with
  | some i => W.take (i + 1)
  | none => W

theorem realEventsL_map (x : Input) (W : List WEv) :
    realEventsL x (W.map fromW) =
      (if x.SendInit' = W64 2 then
        (if (cut0 W).any (fun e => decide (e.t = 3)) then cut0 W else []) else cut0 W).map fromW := by
  have hf : (W.map fromW).findIdx? (fun e => decide (e.ty = evError)) =
      W.findIdx? (fun e => decide (e.t = 4)) := by
    rw [List.findIdx?_map]; congr 1; funext e; simp [fromW_ty_err]
  have hc : (match (W.map fromW).findIdx? (fun e => decide (e.ty = evError)) with
      | some i => (W.map fromW).take (i + 1)
      | none => W.map fromW) = (cut0 W).map fromW := by
    rw [hf]; unfold cut0
    cases W.findIdx? (fun e => decide (e.t = 4)) with
    | none => rfl
    | some i => simp [List.map_take]
  unfold realEventsL
  simp only []
  rw [hc]
  have ha : ((cut0 W).map fromW).any (fun e => decide (e.ty = evBookmark)) =
      (cut0 W).any (fun e => decide (e.t = 3)) := by
    rw [List.any_map]; congr 1; funext e; simp [fromW_ty_bm]
  rw [ha]
  split
  · split <;> rfl
  · rfl

/-- The cut: the events before the first error, then that error if any. -/
theorem cut0_split (W : List WEv) : ∃ N E, cut0 W = N ++ E ∧ (∀ e ∈ N, e.t ≠ 4) ∧
    (∀ e ∈ E, e.t = 4) ∧ E.length ≤ 1 ∧ N <+: nonErr W := by
  unfold cut0
  cases hf : W.findIdx? (fun e => decide (e.t = 4)) with
  | none =>
    rw [List.findIdx?_eq_none_iff] at hf
    have hn : ∀ e ∈ W, e.t ≠ 4 := fun e he => by simpa using hf e he
    refine ⟨W, [], by simp, hn, by simp, by simp, ?_⟩
    unfold nonErr; rw [List.filter_eq_self.2 (fun e he => by simpa using hn e he)]
    exact List.prefix_refl _
  | some i =>
    obtain ⟨hi, hp, hj⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
    have hn : ∀ e ∈ W.take i, e.t ≠ 4 := by
      intro e he
      obtain ⟨j, hj', rfl⟩ := List.getElem_of_mem he
      rw [List.getElem_take]
      have := hj j (by simp at hj'; omega)
      simpa using this
    refine ⟨W.take i, [W[i]], ?_, hn, ?_, by simp, ?_⟩
    · show W.take (i + 1) = _
      rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
    · intro e he; simp at he; subst he; simpa using hp
    · have : nonErr W = nonErr (W.take i) ++ nonErr (W.drop i) := by
        unfold nonErr; rw [← List.filter_append, List.take_append_drop]
      rw [this]
      have h2 : nonErr (W.take i) = W.take i := by
        unfold nonErr; exact List.filter_eq_self.2 (fun e he => by simpa using hn e he)
      rw [h2]; exact List.prefix_append _ _

/-! ### Errors are skipped -/

/-- Not an Error event. -/
def notErrR (e : REv) : Bool := !decide (e.ty = evError)

theorem nonErr_map (L : List WEv) : (nonErr L).map fromW = (L.map fromW).filter notErrR := by
  unfold nonErr notErrR
  rw [List.filter_map]; congr 2; funext e; simp [fromW_ty_err]

theorem evRange_foldl_filter (M : List REv) (acc : Option (w64 × w64)) :
    (M.filter notErrR).foldl evRangeStepR acc = M.foldl evRangeStepR acc := by
  induction M generalizing acc with
  | nil => rfl
  | cons e M ih =>
    by_cases he : e.ty = evError
    · have : notErrR e = false := by simp [notErrR, he]
      rw [List.filter_cons_of_neg (by simp [this]), ih, List.foldl_cons]
      congr 1
      cases acc with
      | none => rfl
      | some p => obtain ⟨a, b⟩ := p; simp [evRangeStepR, he]
    · have : notErrR e = true := by simp [notErrR, he]
      rw [List.filter_cons_of_pos this, List.foldl_cons, List.foldl_cons, ih]

theorem filterBE_filter (M : List REv) : filterBE (M.filter notErrR) = filterBE M := by
  unfold filterBE notErrR
  rw [List.filter_filter]; congr 1; funext e
  by_cases h1 : e.ty = evBookmark <;> by_cases h2 : e.ty = evError <;> simp [h1, h2]

theorem reliableOkR_filter (R : RReplay) (x : Input) (M : List REv) :
    reliableOkR R x (M.filter notErrR) = reliableOkR R x M := by
  unfold reliableOkR watchRangeL evRangeR
  rw [evRange_foldl_filter, filterBE_filter]

/-! ### The bookmarks -/

/-- The bookmark loop's state, by `uint.nat`. -/
def bmNat (p : w64 × w64 × Bool) : Nat × Nat × Bool := (uint.nat p.1, uint.nat p.2.1, p.2.2)

theorem bmStep_rel (L : List WEv) (hL : ∀ e ∈ L, e.t < 5) (s : Option (w64 × w64 × Bool)) :
    ((L.map fromW).foldl bmStepR s).map bmNat = (nonErr L).foldl bmStepL (s.map bmNat) := by
  induction L generalizing s with
  | nil => rfl
  | cons e L ih =>
    have hL' : ∀ e ∈ L, e.t < 5 := fun e' h => hL e' (by simp [h])
    have he5 := hL e (by simp)
    rw [List.map_cons, List.foldl_cons]
    by_cases h4 : e.t = 4
    · have : nonErr (e :: L) = nonErr L := by
        unfold nonErr; rw [List.filter_cons_of_neg (by simp [h4])]
      rw [this, ← ih hL']
      congr 2
      rw [fromW_err e h4]
      cases s with
      | none => rfl
      | some p => obtain ⟨a, b, c⟩ := p; simp [bmStepR]
    · have : nonErr (e :: L) = e :: nonErr L := by
        unfold nonErr; rw [List.filter_cons_of_pos (by simp [h4])]
      rw [this, List.foldl_cons, ih hL']
      congr 1
      have hne : (fromW e).ty ≠ evError := fun h => h4 ((fromW_ty_err e).1 h)
      have ho := fromW_obj e (by omega)
      have hb := fromW_ty_bm e
      cases s with
      | none => rfl
      | some p =>
        obtain ⟨lb, le, f⟩ := p
        simp only [bmStepR, hne, if_false, ho, objRVL, annotL, Option.map_some, bmNat, bmStepL]
        by_cases h3 : e.t = 3
        · have hb' : (fromW e).ty = evBookmark := hb.2 h3
          simp only [hb', h3, if_true]
          by_cases hr : uint.nat e.o.ResourceVersion' < uint.nat lb ∨
              uint.nat e.o.ResourceVersion' < uint.nat le
          · simp [hr]
          · simp only [hr, if_false]
            cases e.o.Annotated' <;> cases f <;> simp [bmNat]
        · have hb' : ¬ (fromW e).ty = evBookmark := fun h => h3 (hb.1 h)
          simp only [hb', h3, if_false]
          by_cases hr : uint.nat e.o.ResourceVersion' ≤ uint.nat lb
          · simp [hr]
          · simp only [hr, if_false, Option.map_some, wmax]
            split <;> simp only [bmNat, Option.some.injEq, Prod.mk.injEq, true_and, and_true] <;> omega

theorem bookmarksOkR_map (L : List WEv) (hL : ∀ e ∈ L, e.t < 5) :
    bookmarksOkR (L.map fromW) = bookmarksOkL (nonErr L) := by
  unfold bookmarksOkR bookmarksOkL
  have := bmStep_rel L hL (some (0, 0, false))
  rw [← Option.isSome_map (f := bmNat), this]; rfl

theorem bookmarksOkL_prefix {L L' : List WEv} (h : bookmarksOkL L = true) (hp : L' <+: L) :
    bookmarksOkL L' = true := by
  obtain ⟨t, rfl⟩ := hp
  unfold bookmarksOkL at h ⊢
  rw [List.foldl_append] at h
  cases hf : L'.foldl bmStepL (some (0, 0, false)) with
  | none => rw [hf, bmStepL_none_foldl] at h; simp at h
  | some _ => rfl

/-! ### The last error -/

theorem lastErrOkL_split (N E : List WEv) (hN : ∀ e ∈ N, e.t ≠ 4) (hE : ∀ e ∈ E, e.t = 4)
    (hlen : E.length ≤ 1) : lastErrOkL ((N ++ E).map fromW) = true := by
  unfold lastErrOkL
  rw [List.all_eq_true]
  rintro ⟨ev, i⟩ hm
  rw [List.mem_zipIdx_iff_getElem?] at hm
  simp only at hm ⊢
  obtain ⟨hi, hev⟩ := List.getElem?_eq_some_iff.1 hm
  subst hev
  simp only [List.length_map, List.length_append] at hi
  rw [List.getElem_map]
  by_cases hiN : i < N.length
  · rw [List.getElem_append_left hiN]
    have : (fromW N[i]).ty ≠ evError := fun h =>
      hN _ (List.getElem_mem hiN) ((fromW_ty_err _).1 h)
    simp [this]
  · rw [List.getElem_append_right (by omega)]
    have h4 := hE _ (List.getElem_mem (l := E) (n := i - N.length) (by omega))
    rw [fromW_err _ h4]
    simp [evError]
    omega

/-! ### The events' range -/

theorem unat_wmin (a b : w64) : uint.nat (wmin a b) = min (uint.nat a) (uint.nat b) := by
  unfold wmin; split <;> omega

theorem unat_wmax (a b : w64) : uint.nat (wmax a b) = max (uint.nat a) (uint.nat b) := by
  unfold wmax; split <;> omega

theorem unat_add_one (a : w64) (h : uint.nat a < 2 ^ 63) : uint.nat (a + W64 1) = uint.nat a + 1 := by
  word

theorem unat_maxU64 : uint.nat maxU64 = 2 ^ 64 - 1 := by decide

/-- One step of `eventResourceVersionRange` on an object event: the least and greatest by its own
range. -/
theorem evRangeStepR_fromW (e : WEv) (he : e.t ≤ 3) (hrv : uint.nat e.o.ResourceVersion' < 2 ^ 63)
    (mn mx : w64) : ∃ lw hw, evRangeStepR (some (mn, mx)) (fromW e) = some (wmin mn lw, wmax mx hw) ∧
      uint.nat lw = evLo e ∧ uint.nat hw = evHi e := by
  have h1 := unat_add_one _ hrv
  have hne : ¬ (evBookmark = evError) := by decide
  by_cases h3 : e.t = 3
  · refine ⟨e.o.ResourceVersion' + W64 1, e.o.ResourceVersion', ?_,
      by simp only [evLo, h3, if_true]; exact h1, by simp [evHi, h3]⟩
    simp [fromW, h3, evRangeStepR, objRVL, evModified, evError, evAdded, evDeleted, evBookmark]
  · refine ⟨e.o.ResourceVersion', e.o.ResourceVersion' + W64 1, ?_, by simp [evLo, h3],
      by simp only [evHi, h3, if_false]; exact h1⟩
    by_cases h0 : e.t = 0
    · simp [fromW, h0, evRangeStepR, objRVL, evAdded, evError]
    by_cases h1' : e.t = 1
    · simp [fromW, h1', evRangeStepR, objRVL, evModified, evError, evAdded, evDeleted]
    have h2 : e.t = 2 := by omega
    simp [fromW, h2, evRangeStepR, objRVL, evModified, evError, evAdded, evDeleted]

/-- The checker's range state against the driver's (none: no event yet). -/
def RelW (w : w64 × w64) : Option (Nat × Nat) → Prop
  | none => w = (maxU64, 0)
  | some (a, b) => uint.nat w.1 = a ∧ uint.nat w.2 = b ∧ a ≤ 2 ^ 63 ∧ b ≤ 2 ^ 63

theorem evRange_rel (L : List WEv) (hL : ∀ e ∈ L, e.t ≤ 3 ∧ uint.nat e.o.ResourceVersion' < 2 ^ 63)
    (w : w64 × w64) (acc : Option (Nat × Nat)) (hw : RelW w acc) :
    ∃ w', (L.map fromW).foldl evRangeStepR (some w) = some w' ∧ RelW w' (L.foldl evRStep acc) := by
  induction L generalizing w acc with
  | nil => exact ⟨w, rfl, hw⟩
  | cons e L ih =>
    obtain ⟨het, herv⟩ := hL e (by simp)
    obtain ⟨lw, hw', hst, hl, hh⟩ := evRangeStepR_fromW e het herv w.1 w.2
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, show (some w) = some (w.1, w.2) from rfl, hst]
    apply ih (fun e' h => hL e' (by simp [h]))
    have hlo : evLo e ≤ 2 ^ 63 := by unfold evLo; split <;> omega
    have hhi : evHi e ≤ 2 ^ 63 := by unfold evHi; split <;> omega
    cases acc with
    | none =>
      simp only [RelW] at hw; rw [hw]
      simp only [evRStep, RelW, unat_wmin, unat_wmax, unat_maxU64]
      have : uint.nat (0 : w64) = 0 := rfl
      omega
    | some p =>
      obtain ⟨a, b⟩ := p
      obtain ⟨h1, h2, h3, h4⟩ := hw
      simp only [evRStep, RelW, unat_wmin, unat_wmax]
      omega

/-- The checker's range of a non-empty list of object events: none, or the driver's. -/
theorem evRangeR_map (L : List WEv) (hL : ∀ e ∈ L, e.t ≤ 3 ∧ uint.nat e.o.ResourceVersion' < 2 ^ 63)
    (lo hi : Nat) (h : evRangeL L = some (lo, hi)) :
    evRangeR (L.map fromW) = some none ∨
      ∃ mn mx, evRangeR (L.map fromW) = some (some (mn, mx)) ∧ uint.nat mn = lo ∧ uint.nat mx = hi := by
  obtain ⟨w', hf, hr⟩ := evRange_rel L hL (maxU64, 0) none rfl
  unfold evRangeL at h
  rw [h] at hr
  obtain ⟨h1, h2, h3, -⟩ := hr
  unfold evRangeR
  rw [hf]
  obtain ⟨a, b⟩ := w'
  simp only []
  by_cases hc : a = maxU64 ∨ b = 0
  · left; rw [if_pos hc]
  · right; exact ⟨a, b, by rw [if_neg hc], h1, h2⟩

/-- The driver's start of the revisions a watch's events mark (`reliableOkL`'s `lo`). -/
def loOf (x : Input) (req l : Nat) : Nat :=
  if x.Match' = W64 1 then (if 0 < req then max l (req + 1) else l) else if 0 < req then req + 1 else l

theorem loOf_mono (x : Input) (req : Nat) {a b : Nat} (h : a ≤ b) : loOf x req a ≤ loOf x req b := by
  unfold loOf; split <;> split <;> omega

theorem loOf_le (x : Input) (req a b : Nat) : loOf x req b ≤ max b (loOf x req a) := by
  unfold loOf; split <;> split <;> omega

theorem watchRangeL_map (x : Input) (L : List WEv)
    (hL : ∀ e ∈ L, e.t ≤ 3 ∧ uint.nat e.o.ResourceVersion' < 2 ^ 63) (lo hi : Nat)
    (h : evRangeL L = some (lo, hi)) (reqw : w64) (hp : parseRVD x.MinRV' = some reqw)
    (hreq : uint.nat reqw < 2 ^ 63) (h2 : ¬ (x.Match' = W64 2 ∧ uint.nat reqw = 0)) :
    watchRangeL x (L.map fromW) = some none ∨
      ∃ mn mx, watchRangeL x (L.map fromW) = some (some (mn, mx)) ∧
        uint.nat mn = loOf x (uint.nat reqw) lo ∧ uint.nat mx = hi := by
  unfold watchRangeL
  rcases evRangeR_map L hL lo hi h with he | ⟨mn, mx, he, h1, h2'⟩
  · rw [he]; exact .inl rfl
  · rw [he]; simp only [hp]
    right
    have ha := unat_add_one reqw hreq
    by_cases hm1 : x.Match' = W64 1
    · refine ⟨_, mx, by rw [if_pos hm1], ?_, h2'⟩
      unfold loOf; rw [if_pos hm1]
      split
      · rw [unat_wmax, ha, h1]
      · exact h1
    · by_cases hm2 : x.Match' = W64 2
      · have hr0 : reqw ≠ 0 := fun e => h2 ⟨hm2, by rw [e]; rfl⟩
        refine ⟨_, mx, by rw [if_neg hm1, if_pos hm2, if_neg hr0], ?_, h2'⟩
        unfold loOf; rw [if_neg hm1, if_pos (by
          have : uint.nat reqw ≠ 0 := fun e => hr0 (by word)
          omega)]
        exact ha
      · refine ⟨_, mx, by rw [if_neg hm1, if_neg hm2], ?_, h2'⟩
        unfold loOf; rw [if_neg hm1]
        split
        · exact ha
        · exact h1

/-! ### The events of a range of revisions -/

theorem mem_eventsInL {x : Input} {hs : List GSt} (hwf : HistWf x hs) {lo hi : Nat} {e : WEv}
    (h : e ∈ eventsInL x hs lo hi) : lo ≤ uint.nat e.o.ResourceVersion' ∧
      uint.nat e.o.ResourceVersion' < hi := by
  unfold eventsInL at h
  obtain ⟨r, hr, he⟩ := List.mem_filterMap.1 h
  rw [List.mem_range'_1] at hr
  rw [(hwf.2.2 r e he).1]; omega

theorem eventsInL_sorted {x : Input} {hs : List GSt} (hwf : HistWf x hs) (lo hi : Nat) :
    (eventsInL x hs lo hi).Pairwise
      (fun a b => uint.nat a.o.ResourceVersion' < uint.nat b.o.ResourceVersion') := by
  unfold eventsInL
  refine List.Pairwise.filterMap _ ?_ (List.pairwise_lt_range' (s := lo) (n := hi - lo))
  intro r r' hr a ha b hb
  rw [(hwf.2.2 r a ha).1, (hwf.2.2 r' b hb).1]; exact hr

theorem eventsInL_window {x : Input} {hs : List GSt} (hwf : HistWf x hs) (lo a b hi : Nat)
    (h1 : lo ≤ a) (h2 : b ≤ hi) :
    (eventsInL x hs lo hi).filter
      (fun e => decide (a ≤ uint.nat e.o.ResourceVersion' ∧ uint.nat e.o.ResourceVersion' < b)) =
      eventsInL x hs a b := by
  by_cases hab : b ≤ a
  · have : eventsInL x hs a b = [] := by unfold eventsInL; rw [show b - a = 0 by omega]; rfl
    rw [this, List.filter_eq_nil_iff]
    intro e _; simp; omega
  rw [eventsInL_split x hs lo a hi h1 (by omega), eventsInL_split x hs a b hi (by omega) h2,
    List.filter_append, List.filter_append]
  rw [List.filter_eq_nil_iff.2 (fun e he => by have := mem_eventsInL hwf he; simp; omega),
    List.filter_eq_self.2 (fun e he => by have := mem_eventsInL hwf he; simp; omega),
    List.filter_eq_nil_iff.2 (fun e he => by have := mem_eventsInL hwf he; simp; omega)]
  simp

theorem filterMap_range'_window {β : Type} (f : Nat → Option β) (c n a b : Nat) (hca : c ≤ a)
    (hb : b ≤ c + n) :
    (List.range' a (b - a)).filterMap f =
      (List.range' c n).filterMap (fun r => if a ≤ r ∧ r < b then f r else none) := by
  by_cases hab : b ≤ a
  · rw [show b - a = 0 by omega, List.range'_zero, List.filterMap_nil]
    symm; rw [List.filterMap_eq_nil_iff]
    intro r _; rw [if_neg (by omega)]
  have hr : List.range' c n = List.range' c (a - c) ++ (List.range' a (b - a) ++
      List.range' b (c + n - b)) := by
    have e1 := @List.range'_append_1 c (a - c) ((b - a) + (c + n - b))
    have e2 := @List.range'_append_1 a (b - a) (c + n - b)
    rw [show c + (a - c) = a by omega] at e1
    rw [show a + (b - a) = b by omega] at e2
    rw [e2, e1]; congr 1; omega
  have e3 : (List.range' c (a - c)).filterMap (fun r => if a ≤ r ∧ r < b then f r else none) = [] :=
    List.filterMap_eq_nil_iff.2 (fun r hr => by rw [List.mem_range'_1] at hr; rw [if_neg (by omega)])
  have e4 : (List.range' b (c + n - b)).filterMap (fun r => if a ≤ r ∧ r < b then f r else none) = [] :=
    List.filterMap_eq_nil_iff.2 (fun r hr => by rw [List.mem_range'_1] at hr; rw [if_neg (by omega)])
  rw [hr, List.filterMap_append, List.filterMap_append, e3, e4, List.nil_append, List.append_nil]
  exact filterMap_congr' (fun r hr => by rw [List.mem_range'_1] at hr; rw [if_pos (by omega)])

/-! ### The replay's events are the history's -/

theorem toWatchEventL_chg (x : Input) (k : GoString) (ch : Chg) (r : Nat) (hr : ch.rv = r) :
    toWatchEventL x ⟨k, W64 (r : Int), ch.cur, ch.prev⟩ = (toEventL x ch).map fromW := by
  unfold toWatchEventL toEventL
  simp only []
  rw [hr]
  cases hc : ch.cur with
  | none =>
    cases hp : ch.prev with
    | none => simp
    | some p => by_cases hs : selOkL x p <;> simp [hs, fromW]
  | some c =>
    cases hp : ch.prev with
    | none => by_cases hs : selOkL x c <;> simp [hs, fromW]
    | some p => by_cases hs : selOkL x c <;> by_cases hs' : selOkL x p <;> simp [hs, hs', fromW]

/-- **The replay's events over a range of revisions** (at most the configuration's) are the
history's from `s0` on. -/
theorem eventsForRVsL_eq (s0 : w64) (R : RReplay) (h : HSt) (x : Input)
    (hlen : h.hist.length = uint.nat h.st.rv) (hwf : HistWf x h.hist) (hs0 : 1 ≤ uint.nat s0)
    (hs0h : uint.nat s0 ≤ uint.nat h.st.rv) (hR : ReplayAt s0 R h) (mn mx : w64)
    (hmx : uint.nat mx ≤ uint.nat h.st.rv + 1) :
    eventsForRVsL R x mn mx =
      (eventsInL x h.hist (max (uint.nat mn) (uint.nat s0 + 1)) (uint.nat mx)).map fromW := by
  have hb := hwf.1
  unfold eventsForRVsL
  have hfil : R.changes.filterMap (fun c =>
      if uint.nat mn ≤ uint.nat c.rv ∧ uint.nat c.rv < uint.nat mx ∧
        keyInScopeL x.WKey' x.Recursive' c.key = true then toWatchEventL x c else none) =
      (R.changes.filter (fun c => decide (uint.nat c.rv ≤ uint.nat h.st.rv))).filterMap (fun c =>
      if uint.nat mn ≤ uint.nat c.rv ∧ uint.nat c.rv < uint.nat mx ∧
        keyInScopeL x.WKey' x.Recursive' c.key = true then toWatchEventL x c else none) := by
    rw [List.filterMap_filter]
    refine filterMap_congr' (fun c _ => ?_)
    by_cases hc : uint.nat c.rv ≤ uint.nat h.st.rv
    · simp [hc]
    · simp only [hc, decide_false, Bool.false_eq_true, if_false]
      rw [if_neg (by omega)]
  rw [hfil, hR.2]
  unfold chgListL eventsInL
  rw [List.filterMap_filterMap, List.map_filterMap,
    filterMap_range'_window _ (uint.nat s0 + 1) (h.hist.length - uint.nat s0) _ _ (by omega)
      (by omega)]
  refine filterMap_congr' (fun r hr => ?_)
  rw [List.mem_range'_1] at hr
  have hr64 : uint.nat (W64 (r : Int)) = r := W64_nat r (by omega)
  have h2 : 2 ≤ r := by omega
  unfold evAtL
  rw [if_pos h2]
  cases hc : changeAtL (k8s_etcd3.histN h.hist (r - 1)).items (k8s_etcd3.histN h.hist r).items r with
  | none =>
    simp only [Option.map_none, Option.bind_none]
    split <;> rfl
  | some ch =>
    have hcr := changeAtL_rv _ _ _ _ hc
    simp only [Option.map_some, Option.bind_some, hr64]
    by_cases hw : max (uint.nat mn) (uint.nat s0 + 1) ≤ r ∧ r < uint.nat mx
    · rw [if_pos hw]
      by_cases hk : keyInScopeL x.WKey' x.Recursive' (storeKeyL ch.key) = true
      · rw [if_pos ⟨by omega, hw.2, hk⟩, if_pos hk, toWatchEventL_chg x _ ch r hcr]
      · rw [if_neg (fun h => hk h.2.2), if_neg hk]; rfl
    · rw [if_neg hw, if_neg (fun h => hw ⟨by omega, h.2.1⟩)]

/-! ### The order of bookmarks and events -/

/-- A bookmark comes before a later event only at a smaller revision (`validateBookmarks`). -/
def BmOrd (d e : WEv) : Prop :=
  d.t = 3 → e.t ≠ 3 → uint.nat d.o.ResourceVersion' < uint.nat e.o.ResourceVersion'

theorem bmOrd_foldl : ∀ (L : List WEv) (lb le : Nat) (ann : Bool),
    (L.foldl bmStepL (some (lb, le, ann))).isSome = true →
    L.Pairwise BmOrd ∧ ∀ e ∈ L, e.t ≠ 3 → lb < uint.nat e.o.ResourceVersion'
  | [], _, _, _, _ => ⟨List.Pairwise.nil, by simp⟩
  | e :: L, lb, le, ann, h => by
    rw [List.foldl_cons] at h
    by_cases h3 : e.t = 3
    · by_cases hr : uint.nat e.o.ResourceVersion' < lb ∨ uint.nat e.o.ResourceVersion' < le
      · have : bmStepL (some (lb, le, ann)) e = none := by simp [bmStepL, h3, hr]
        rw [this, bmStepL_none_foldl] at h; simp at h
      · have hc : bmStepL (some (lb, le, ann)) e = none ∨
            ∃ a', bmStepL (some (lb, le, ann)) e = some (uint.nat e.o.ResourceVersion', le, a') := by
          simp only [bmStepL, h3, if_true, hr, if_false]
          split
          · split
            · exact .inl rfl
            · exact .inr ⟨_, rfl⟩
          · exact .inr ⟨_, rfl⟩
        rcases hc with hc | ⟨a', hc⟩
        · rw [hc, bmStepL_none_foldl] at h; simp at h
        · rw [hc] at h
          obtain ⟨ih1, ih2⟩ := bmOrd_foldl L _ _ _ h
          refine ⟨List.pairwise_cons.2 ⟨fun e' he' _ h3' => ih2 e' he' h3', ih1⟩, ?_⟩
          intro e' he' h3'
          rcases List.mem_cons.1 he' with rfl | he'
          · exact absurd h3 h3'
          · have := ih2 e' he' h3'; omega
    · by_cases hr : uint.nat e.o.ResourceVersion' ≤ lb
      · have : bmStepL (some (lb, le, ann)) e = none := by simp [bmStepL, h3, hr]
        rw [this, bmStepL_none_foldl] at h; simp at h
      · have hc : bmStepL (some (lb, le, ann)) e =
            some (lb, max le (uint.nat e.o.ResourceVersion'), ann) := by
          simp [bmStepL, h3, hr]
        rw [hc] at h
        obtain ⟨ih1, ih2⟩ := bmOrd_foldl L _ _ _ h
        refine ⟨List.pairwise_cons.2 ⟨fun e' _ h3' => absurd h3' h3, ih1⟩, ?_⟩
        intro e' he' h3'
        rcases List.mem_cons.1 he' with rfl | he'
        · omega
        · exact ih2 e' he' h3'

theorem bmOrd_of_bookmarksOkL (L : List WEv) (h : bookmarksOkL L = true) : L.Pairwise BmOrd :=
  (bmOrd_foldl L 0 0 false h).1

/-! ### Comparisons -/

theorem evsEqL_eq {a b : List WEv} (h : evsEqL a b = true) : a = b := by
  unfold evsEqL at h
  have h' := of_decide_eq_true h
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons _ _ => simp at h'
  | cons e a ih =>
    cases b with
    | nil => simp at h'
    | cons e' b =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h'
      obtain ⟨⟨h1, h2⟩, h3⟩ := h'
      have : e = e' := by cases e; cases e'; simp_all
      rw [this, ih (by simp [h3]) h3]

theorem mapM_evRefL (M : List REv) (h : ∀ e ∈ M, ∃ o, e.o = .obj o) :
    ∃ rs, M.mapM evRefL = some rs := by
  induction M with
  | nil => exact ⟨[], rfl⟩
  | cons e M ih =>
    obtain ⟨rs, hrs⟩ := ih (fun e' h' => h e' (by simp [h']))
    obtain ⟨o, ho⟩ := h e (by simp)
    obtain ⟨ty, o'⟩ := e
    simp only at ho; subst ho
    exact ⟨(storeKeyL (o.Namespace' ++ go!"/" ++ o.Name'), ty, o.ResourceVersion') :: rs,
      by simp [List.mapM_cons, hrs, evRefL, keyOfL, objRVL]⟩

theorem compareEventsL_self (M : List REv) (h : ∀ e ∈ M, ∃ o, e.o = .obj o) :
    compareEventsL M M = true := by
  obtain ⟨rs, hrs⟩ := mapM_evRefL M h
  unfold compareEventsL; rw [hrs]; simp

theorem fromW_objs (L : List WEv) (h : ∀ e ∈ L, e.t ≤ 3) : ∀ e ∈ L.map fromW, ∃ o, e.o = .obj o := by
  intro e he
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 he
  exact ⟨w.o, fromW_obj w (h w hw)⟩

theorem filterBE_map (L : List WEv) (h : ∀ e ∈ L, e.t ≤ 3) :
    filterBE (L.map fromW) = (L.filter fun e => decide (e.t ≠ 3)).map fromW := by
  unfold filterBE
  rw [List.filter_map]
  congr 1
  refine List.filter_congr (fun e he => ?_)
  have h4 : e.t ≠ 4 := by have := h e he; omega
  have hb := fromW_ty_bm e
  have he' := fromW_ty_err e
  by_cases h3 : e.t = 3
  · simp [Function.comp, hb.2 h3, h3]
  · have : ¬ (fromW e).ty = evBookmark := fun x => h3 (hb.1 x)
    have : ¬ (fromW e).ty = evError := fun x => h4 (he'.1 x)
    simp [Function.comp, *]

theorem nonErr_append_err (M E : List WEv) (hM : ∀ e ∈ M, e.t ≠ 4) (hE : ∀ e ∈ E, e.t = 4) :
    nonErr (M ++ E) = M := by
  unfold nonErr
  rw [List.filter_append, List.filter_eq_self.2 (fun e he => by simpa using hM e he),
    List.filter_eq_nil_iff.2 (fun e he => by simpa using hE e he), List.append_nil]

theorem reliableOkR_append_err (R : RReplay) (x : Input) (M E : List WEv) (hM : ∀ e ∈ M, e.t ≠ 4)
    (hE : ∀ e ∈ E, e.t = 4) : reliableOkR R x ((M ++ E).map fromW) = reliableOkR R x (M.map fromW) := by
  rw [← reliableOkR_filter R x ((M ++ E).map fromW), ← nonErr_map, nonErr_append_err M E hM hE]

/-! ### The reliable part -/

/-- **The reliable part of a prefix.** If the driver's `reliableOk` accepts the events `T` (no
errors; revisions at most the configuration's; bookmarks before later events; all after `s0`),
the checker's `validateReliable` accepts any prefix of them. -/
theorem reliableOkR_prefix (s0 : w64) (R : RReplay) (h : HSt) (x : Input) (reqw : w64)
    (T T' : List WEv)
    (hlen : h.hist.length = uint.nat h.st.rv) (hwf : HistWf x h.hist) (hs0 : 1 ≤ uint.nat s0)
    (hs0h : uint.nat s0 ≤ uint.nat h.st.rv) (hR : ReplayAt s0 R h)
    (hp : parseRVD x.MinRV' = some reqw) (hreq : uint.nat reqw < 2 ^ 63)
    (ht : ∀ e ∈ T, e.t ≤ 3) (hrv : ∀ e ∈ T, uint.nat e.o.ResourceVersion' ≤ uint.nat h.st.rv)
    (hord : T.Pairwise BmOrd) (hfrom : ∀ e ∈ T, uint.nat s0 < evLo e)
    (hrel : reliableOkL x (uint.nat reqw) T h = true) (hpre : T' <+: T) :
    reliableOkR R x (T'.map fromW) = true := by
  have hH : uint.nat h.st.rv < 2 ^ 63 := hlen ▸ hwf.1
  obtain ⟨U, rfl⟩ := hpre
  cases T' with
  | nil => simp [reliableOkR, watchRangeL, evRangeR]
  | cons d T1 =>
    have hmemT : ∀ e ∈ d :: T1, e ∈ d :: T1 ++ U := fun e he => List.mem_append_left _ he
    obtain ⟨lo0, hi, hT, hlo0, -, hhi, -⟩ := evRangeL_cons d (T1 ++ U)
    obtain ⟨lo1, hi1, hT1, hlo1, ⟨d1, hd1, hd1eq⟩, hhi1, ⟨d', hd', hd'eq⟩⟩ := evRangeL_cons d T1
    unfold reliableOkL at hrel
    rw [show d :: T1 ++ U = d :: (T1 ++ U) from rfl, hT] at hrel
    simp only at hrel
    split at hrel
    · cases hrel
    rename_i h2
    split at hrel
    · cases hrel
    rename_i hhiH
    have hE := evsEqL_eq hrel
    change eventsInL x h.hist (loOf x (uint.nat reqw) lo0) hi = _ at hE
    rw [show d :: (T1 ++ U) = (d :: T1) ++ U from rfl] at hE hlo0 hhi
    have hL1 : ∀ e ∈ d :: T1, e.t ≤ 3 ∧ uint.nat e.o.ResourceVersion' < 2 ^ 63 :=
      fun e he => ⟨ht e (hmemT e he), by have := hrv e (hmemT e he); omega⟩
    rcases watchRangeL_map x (d :: T1) hL1 lo1 hi1 hT1 reqw hp hreq h2 with hw | ⟨mn, mx, hw, hmn, hmx⟩
    · unfold reliableOkR; rw [hw]
    unfold reliableOkR; rw [hw]; simp only []
    have hi1hi : hi1 ≤ hi := hd'eq ▸ hhi d' (hmemT d' hd')
    rw [eventsForRVsL_eq s0 R h x hlen hwf hs0 hs0h hR mn mx (by omega),
      filterBE_map _ (fun e he => ht e (hmemT e he))]
    have hlo01 : lo0 ≤ lo1 := hd1eq ▸ hlo0 d1 (hmemT d1 hd1)
    have hwin : eventsInL x h.hist (max (uint.nat mn) (uint.nat s0 + 1)) (uint.nat mx) =
        (d :: T1).filter (fun e => decide (e.t ≠ 3)) := by
      rw [← eventsInL_window hwf (loOf x (uint.nat reqw) lo0) _ _ hi
        (by have := loOf_mono x (uint.nat reqw) hlo01; omega) (by omega), hE, List.filter_append]
      have hsorted := eventsInL_sorted hwf (x := x) (hs := h.hist) (loOf x (uint.nat reqw) lo0) hi
      rw [hE, List.filter_append, List.pairwise_append] at hsorted
      have hB : (U.filter (fun e => decide (e.t ≠ 3))).filter (fun e => decide
          (max (uint.nat mn) (uint.nat s0 + 1) ≤ uint.nat e.o.ResourceVersion' ∧
            uint.nat e.o.ResourceVersion' < uint.nat mx)) = [] := by
        refine List.filter_eq_nil_iff.2 (fun e he => ?_)
        have he3 : e.t ≠ 3 := by simpa using (List.mem_filter.1 he).2
        have heU := (List.mem_filter.1 he).1
        have : uint.nat mx ≤ uint.nat e.o.ResourceVersion' := by
          rw [hmx, hd'eq]
          by_cases hd3 : d'.t = 3
          · have := (List.pairwise_append.1 hord).2.2 d' hd' e heU hd3 he3
            simp only [evHi, hd3, if_true]; omega
          · have := hsorted.2.2 d' (List.mem_filter.2 ⟨hd', by simpa using hd3⟩) e he
            simp only [evHi, hd3, if_false]; omega
        simp; omega
      have hA : ((d :: T1).filter (fun e => decide (e.t ≠ 3))).filter (fun e => decide
          (max (uint.nat mn) (uint.nat s0 + 1) ≤ uint.nat e.o.ResourceVersion' ∧
            uint.nat e.o.ResourceVersion' < uint.nat mx)) = (d :: T1).filter (fun e => decide (e.t ≠ 3)) := by
        refine List.filter_eq_self.2 (fun e he => ?_)
        have he3 : e.t ≠ 3 := by simpa using (List.mem_filter.1 he).2
        have heT := (List.mem_filter.1 he).1
        have hlo : evLo e = uint.nat e.o.ResourceVersion' := by simp [evLo, he3]
        have hf := hfrom e (hmemT e heT)
        have h1 := hlo1 e heT
        have h2' := hhi1 e heT
        have hin := mem_eventsInL hwf (show e ∈ eventsInL x h.hist (loOf x (uint.nat reqw) lo0) hi by
          rw [hE, List.filter_append]; exact List.mem_append_left _ he)
        have hle := loOf_le x (uint.nat reqw) lo0 lo1
        simp only [evHi, he3, if_false] at h2'
        simp only [decide_eq_true_eq]
        omega
      rw [List.filter_append, hA, hB, List.append_nil]
    rw [hwin]
    exact compareEventsL_self _ (fromW_objs _ (fun e he => ht e (hmemT e (List.mem_filter.1 he).1)))

/-! ### The initial events -/

theorem ofList_isSome (l : List (GoString × Obj)) (k : GoString) :
    (GMap.ofList l !! k).isSome ↔ k ∈ l.map Prod.fst := by
  induction l with
  | nil => show ((∅ : GMap GoString Obj) !! k).isSome ↔ _; simp
  | cons a l ih =>
    obtain ⟨k', v⟩ := a
    show (<[k' := v]> (GMap.ofList l) !! k).isSome ↔ _
    rw [GMap.lookup_insert_eq_iff]
    by_cases h : k' = k
    · subst h; simp
    · simp only [h, if_false, ih, List.map_cons, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (e | e)
        · exact absurd e.symm h
        · exact e

theorem fI_mem (its : List item) (hs : SortedI its) (it : item) (h : it ∈ its) :
    fI its it.key' = some it := by
  induction its with
  | nil => cases h
  | cons e es ih =>
    obtain ⟨hs', hlt⟩ := sortedI_cons' hs
    rw [fI_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · simp
    · have hne : e.key' ≠ it.key' := by
        intro he
        unfold SortedI at hs
        simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hs
        exact go.goStringLt_irrefl it.key' (he ▸ hs.1 it.key' ⟨it, h', rfl⟩)
      rw [if_neg hne]; exact ih hs' h'

/-- **The checker's items of a sorted store's model** are its items, in order, at their store keys. -/
theorem itemsL_absR (st : GSt) (hs : SortedI st.items) :
    itemsL (absR st) = st.items.map fun it => (storeKeyL it.key', it.obj') := by
  unfold itemsL
  have hk : sortedKeysL (absR st).items = st.items.map fun it => storeKeyL it.key' := by
    symm
    apply sortedKeysL_unique
    · intro k
      simp only [absR]
      rw [ofList_isSome, List.map_map]; rfl
    · unfold SortedI at hs
      rw [List.pairwise_map] at hs ⊢
      exact hs.imp fun h => (storeKeyL_lt _ _).2 h
  rw [hk, List.filterMap_map, ← List.filterMap_eq_map]
  refine filterMap_congr' (fun it hit => ?_)
  simp only [Function.comp, absR]
  rw [ofList_items, fI_mem _ hs it hit]; rfl

theorem initialEventsL_absR (x : Input) (st : GSt) (hs : SortedI st.items) :
    (initialEventsL x st).map fromW =
      (listItemsL x x.WKey' (absR st)).map fun o => (⟨evAdded, .obj o⟩ : REv) := by
  unfold initialEventsL listItemsL scopeR
  rw [itemsL_absR st hs]
  simp only [List.map_map, List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr; intro it _; simp [Function.comp, Bool.and_comm]

/-! ### The first bookmark -/

theorem dropWhile_findIdx (L : List WEv) (b : Nat)
    (h : L.findIdx? (fun e => decide (e.t = 3)) = some b) :
    L.dropWhile (fun e => decide (e.t ≠ 3)) = L.drop b := by
  induction L generalizing b with
  | nil => simp at h
  | cons e L ih =>
    rw [List.findIdx?_cons] at h
    rw [List.dropWhile_cons]
    by_cases h3 : e.t = 3
    · simp only [h3, decide_true, if_true, Option.some.injEq] at h
      subst h; simp [h3]
    · simp only [h3, decide_false, Bool.false_eq_true, if_false] at h
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 h
      simp only [h3, ne_eq, not_false_eq_true, decide_true, if_true, List.drop_succ_cons]
      exact ih b' hb'

/-! ## B5 -/

/-- **B5.** A watch of `x` that ran (not skipped, its `Watch` call did not fail), whose output's
events decode to the driver's view of the received events `raw` and which the driver's check
accepts at the configuration `h`, is accepted by `ValidateWatch` on `realEvents(in, raw)`, against
a replay that agrees with `h` from the seeded revision `s0` on. -/
theorem validateWatchL_of_watchOkL (s0 : w64) (R : RReplay) (h : HSt) (x : Input) (y : Output)
    (raw : List REv)
    (hlen : h.hist.length = uint.nat h.st.rv) (hwf : HistWf x h.hist) (hsort : HistSorted h.hist)
    (hs0 : 1 ≤ uint.nat s0) (hs0h : uint.nat s0 ≤ uint.nat h.st.rv)
    (hR : ReplayAt s0 R h)
    (hreq : ∀ n, parseRVD x.MinRV' = some n → uint.nat n < 2 ^ 63)
    (hskip : x.Skip' = false) (hfail : y.WFailed' = false)
    (hdec : decWEventsL y.WEvents' = some (raw.map toWEvL))
    (hfrom : WatchFromL s0 x (raw.map toWEvL))
    (hok : watchOkL x y h = true) :
    validateWatchL R x (realEventsL x raw) = true := by
  have hH : uint.nat h.st.rv < 2 ^ 63 := hlen ▸ hwf.1
  unfold watchOkL at hok
  rw [hfail, hskip, hdec] at hok
  simp only [Bool.or_false, Bool.false_eq_true, if_false] at hok
  generalize hW : raw.map toWEvL = W at hok hfrom
  split at hok
  · cases hok
  rename_i h5
  split at hok
  · cases hok
  rename_i hrvb
  split at hok
  · cases hok
  rename_i hbm
  split at hok
  · cases hok
  rename_i reqw hp
  have hreqw := hreq reqw hp
  have h5' : ∀ e ∈ W, e.t < 5 := fun e he => by
    have := List.any_eq_false.1 (Bool.eq_false_iff.2 h5) e he
    simp only [decide_eq_true_eq] at this; omega
  have hrv' : ∀ e ∈ nonErr W, uint.nat e.o.ResourceVersion' ≤ uint.nat h.st.rv := fun e he => by
    have := List.any_eq_false.1 (Bool.eq_false_iff.2 hrvb) e he
    simp only [decide_eq_true_eq] at this; omega
  have hbm' : bookmarksOkL (nonErr W) = true := by unfold nonErr; simpa using hbm
  have ht : ∀ e ∈ nonErr W, e.t ≤ 3 := fun e he => by
    have h1 := List.mem_filter.1 he
    have := h5' e h1.1
    simp only [decide_eq_true_eq] at h1; omega
  have hord := bmOrd_of_bookmarksOkL _ hbm'
  have hraw : raw = W.map fromW := by
    rw [← hW, List.map_map]
    refine (List.map_id raw).symm.trans (List.map_congr_left (fun e he => ?_))
    exact (fromW_toWEvL e (h5' _ (by rw [← hW]; exact List.mem_map_of_mem he))).symm
  rw [hraw, realEventsL_map]
  obtain ⟨N, E, hc, hN, hE, hE1, hNp⟩ := cut0_split W
  obtain ⟨Np, hNp'⟩ := hNp
  have hNW : ∀ e ∈ N, e ∈ nonErr W := fun e he => hNp' ▸ List.mem_append_left _ he
  rw [hc]
  have hNE5 : ∀ e ∈ N ++ E, e.t < 5 := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · have := ht e (hNW e he); omega
    · have := hE e he; omega
  have hlast := lastErrOkL_split N E hN hE hE1
  have hbmR : bookmarksOkR ((N ++ E).map fromW) = true := by
    rw [bookmarksOkR_map _ hNE5, nonErr_append_err N E hN hE]
    exact bookmarksOkL_prefix hbm' ⟨Np, hNp'⟩
  by_cases hsi : x.SendInit' = W64 2
  · rw [if_pos hsi] at hok
    rw [if_pos hsi]
    by_cases hb : (N ++ E).any (fun e => decide (e.t = 3)) = true
    · rw [if_pos hb]
      have hEb : E.any (fun e => decide (e.t = 3)) = false :=
        List.any_eq_false.2 (fun e he => by have := hE e he; simp [this])
      have hbN : (N.findIdx? (fun e => decide (e.t = 3))).isSome := by
        rw [List.findIdx?_isSome]; rw [List.any_append, hEb, Bool.or_false] at hb; exact hb
      obtain ⟨b, hbN'⟩ := Option.isSome_iff_exists.1 hbN
      obtain ⟨hbl, hb3, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hbN'
      have hb3' : N[b].t = 3 := by simpa using hb3
      have hbW : (nonErr W).findIdx? (fun e => decide (e.t = 3)) = some b := by
        rw [← hNp', List.findIdx?_append, hbN']; rfl
      change (match (nonErr W).findIdx? (fun e => decide (e.t = 3)) with
        | none => _ | some b => _) = true at hok
      rw [hbW] at hok
      simp only [] at hok
      have hgd : (W.filter fun e => decide (e.t ≠ 4)).getD b ⟨0, ⟨[], [], [], [], [], [], 0, false⟩⟩ =
          N[b] := by
        show (nonErr W).getD b _ = _
        rw [← hNp', List.getD_eq_getElem?_getD, List.getElem?_append_left hbl,
          List.getElem?_eq_getElem hbl]; rfl
      rw [hgd] at hok
      split at hok
      · cases hok
      rename_i hann
      split at hok
      · cases hok
      rename_i hcond
      split at hok
      · cases hok
      rename_i hinit
      have hann' : N[b].o.Annotated' = true := by simpa using hann
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hinit
      have hinit' : initialEventsL x (k8s_etcd3.histN h.hist (uint.nat N[b].o.ResourceVersion')) =
          (nonErr W).take b := evsEqL_eq hinit
      have hdropN : ∀ e ∈ N.drop b, e.t ≠ 4 := fun e he => hN e (List.mem_of_mem_drop he)
      -- the start of the reliable part, after `s0`
      have hdrop : (nonErr W).dropWhile (fun e => decide (e.t ≠ 3)) = (nonErr W).drop b :=
        dropWhile_findIdx _ b hbW
      have hfromT : ∀ e ∈ (nonErr W).drop b, uint.nat s0 < evLo e := by
        unfold WatchFromL at hfrom; rw [if_pos hsi, hdrop] at hfrom; exact hfrom
      have hdropW : (nonErr W).drop b = N.drop b ++ Np := by
        rw [← hNp', List.drop_append_of_le_length (by omega)]
      have hbmem : N[b] ∈ (nonErr W).drop b := by
        rw [hdropW, List.drop_eq_getElem_cons hbl]
        exact List.mem_append_left _ (List.mem_cons_self ..)
      have hs0b : uint.nat s0 ≤ uint.nat N[b].o.ResourceVersion' := by
        have := hfromT _ hbmem; simp only [evLo, hb3', if_true] at this; omega
      have hbH : uint.nat N[b].o.ResourceVersion' ≤ uint.nat h.st.rv :=
        hrv' _ (hNW _ (List.getElem_mem hbl))
      unfold validateWatchL
      rw [hlast, hbmR, if_pos hsi]
      simp only [Bool.true_and]
      have hsplit : splitInitL ((N ++ E).map fromW) =
          some ((N.take b).map fromW, (N.drop b ++ E).map fromW) := by
        unfold splitInitL
        rw [List.findIdx?_map]
        have hp3 : ((fun e : REv => decide (e.ty = evBookmark)) ∘ fromW) = (fun e => decide (e.t = 3)) := by
          funext e; simp [fromW_ty_bm]
        rw [hp3, List.findIdx?_append, hbN']
        simp only [Option.some_or]
        have hgb : ((N ++ E).map fromW).getD b ⟨[], .other⟩ = fromW N[b] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_append_left hbl,
            List.getElem?_eq_getElem hbl]; rfl
        rw [hgb, fromW_obj _ (by omega)]
        simp only [annotL, hann']
        rw [← List.map_take, ← List.map_drop, List.take_append_of_le_length (by omega),
          List.drop_append_of_le_length (by omega)]
      rw [hsplit, List.drop_eq_getElem_cons hbl, List.cons_append, List.map_cons]
      simp only [fromW_obj _ (show N[b].t ≤ 3 by omega), objRVL]
      rw [← List.map_cons, ← List.cons_append, ← List.drop_eq_getElem_cons hbl,
        reliableOkR_append_err R x _ E hdropN hE, Bool.and_eq_true]
      constructor
      · -- the initial events
        unfold initialOkL
        rw [Bool.and_eq_true]
        constructor
        · split
          · rw [hp]; simp only [decide_eq_true_eq]; omega
          · rfl
        · unfold initialEventsR
          rw [hR.1 _ hs0b hbH]
          simp only [Option.map_some]
          have htk : N.take b = initialEventsL x (k8s_etcd3.histN h.hist (uint.nat N[b].o.ResourceVersion')) := by
            rw [hinit', ← hNp', List.take_append_of_le_length (by omega)]
          rw [htk, initialEventsL_absR x _ (hsort _ (by omega))]
          refine compareEventsL_self _ (fun e he => ?_)
          obtain ⟨o, -, rfl⟩ := List.mem_map.1 he
          exact ⟨o, rfl⟩
      · -- the events from the bookmark on
        exact reliableOkR_prefix s0 R h x reqw ((nonErr W).drop b) (N.drop b) hlen hwf hs0 hs0h hR hp
          hreqw (fun e he => ht e (List.mem_of_mem_drop he))
          (fun e he => hrv' e (List.mem_of_mem_drop he)) (hord.sublist (List.drop_sublist _ _))
          hfromT hok ⟨Np, hdropW.symm⟩
    · rw [if_neg hb]
      simp [validateWatchL, lastErrOkL, bookmarksOkR, splitInitL, filterBE, hsi]
  · rw [if_neg hsi] at hok
    rw [if_neg hsi]
    unfold validateWatchL
    rw [hlast, hbmR, if_neg hsi]
    simp only [Bool.true_and]
    rw [reliableOkR_append_err R x N E hN hE]
    have hfromT : ∀ e ∈ nonErr W, uint.nat s0 < evLo e := by
      unfold WatchFromL at hfrom; rw [if_neg hsi] at hfrom; exact hfrom
    exact reliableOkR_prefix s0 R h x reqw (nonErr W) N hlen hwf hs0 hs0h hR hp hreqw ht hrv' hord
      hfromT hok ⟨Np, hNp'⟩

end go

end k8s_correctness
end EtcdGrove
end Perennial
