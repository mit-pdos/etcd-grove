/-
Lean-first (no Rocq counterpart).

# The watch check accepts the watches the store delivers (stage 7f-2 of `notes/k8s-7f-scope.md`)

What a watch of the etcd3 store delivers, stated over the store's history `hs` (the store at each
revision, `hs[R-1]` at `R`), and the obligation behind the driver's closed theorem with watches:
**`watchOkL_of_stream`**, the driver's check (`watchOkL`, `KWatch.lean`) accepts every such watch
against the configuration whose history is `hs` (the real one, 7e's invariant).

- `TailOk x hs c es`: the events `es` of a watch of `x` from the cursor `c` (the last revision it
  reported): change events in revision order, none missing (`evAtL`), and progress bookmarks at
  revisions with no change in scope since the cursor;
- `StreamOkL x req hs evs`: the events a watch delivered, Error events anywhere (the etcd3 watcher
  can send events after one, `nonissues/k8s-etcd3-watcher-events-after-error.md`): for a
  watch-list, the initial events at some revision `r0 ≥ req` (all of them followed by the
  initial-events-end bookmark at `r0` and a tail from `r0`, or a prefix of them if the watch
  ended before); otherwise a tail from the requested revision (any, for RV 0: the store's
  current one when the watch started);
- `HistWf x hs`: what the model's histories satisfy (the objects carry their revisions, no
  annotation, revisions below `2^63`), a premise here, proved of the model's histories in 7f-6.

The store's watch spec (7f-5a) delivers `StreamOkL` over etcd's history read as stores; 7e's
invariant identifies that with the matching configuration's `hist`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts]

/-- A watch's events from the cursor `c` (see the file header). -/
inductive TailOk (x : Input) (hs : List GSt) : Nat → List WEv → Prop
  | nil (c : Nat) : TailOk x hs c []
  | ev (c r : Nat) (e : WEv) (rest : List WEv) : c < r → r ≤ hs.length →
      (∀ r', c < r' → r' < r → evAtL x hs r' = none) → evAtL x hs r = some e →
      TailOk x hs r rest → TailOk x hs c (e :: rest)
  | bm (c p : Nat) (o : Obj) (rest : List WEv) : c ≤ p → p ≤ hs.length →
      uint.nat o.ResourceVersion' = p →
      (∀ r', c < r' → r' ≤ p → evAtL x hs r' = none) →
      TailOk x hs p rest → TailOk x hs c (⟨3, o⟩ :: rest)

/-- The bookmarks among the events carry no annotation (progress notifications). -/
def NoAnn (es : List WEv) : Prop := ∀ e ∈ es, e.t = 3 → e.o.Annotated' = false

/-- The events that are not errors. -/
def nonErr (evs : List WEv) : List WEv := evs.filter fun e => e.t ≠ 4

/-- What a watch of `x`, requested from the revision `req`, delivered (see the file header). -/
def StreamOkL (x : Input) (req : Nat) (hs : List GSt) (evs : List WEv) : Prop :=
  (∀ e ∈ evs, e.t ≤ 4) ∧
  if x.SendInit' = W64 2 then
    ∃ r0, max req 1 ≤ r0 ∧ r0 ≤ hs.length ∧
      (nonErr evs <+: initialEventsL x (histN hs r0) ∨
        ∃ (o : Obj) (tail : List WEv), uint.nat o.ResourceVersion' = r0 ∧ o.Annotated' = true ∧
          nonErr evs = initialEventsL x (histN hs r0) ++ ⟨3, o⟩ :: tail ∧ TailOk x hs r0 tail ∧
          NoAnn tail)
  else ∃ s0, (0 < req → s0 = req) ∧ TailOk x hs s0 (nonErr evs) ∧ NoAnn (nonErr evs)

/-- The requests the driver makes (`genWatch`): a watch-list asks for NotOlderThan; RV 0 without
a watch-list asks for `SendInitialEvents = false` and NotOlderThan; any other RV the legacy match. -/
def WatchInOk (x : Input) (req : Nat) : Prop :=
  (x.SendInit' = W64 2 → x.Match' = W64 1) ∧
  (x.SendInit' ≠ W64 2 → (req = 0 ∧ x.Match' = W64 1) ∨ (0 < req ∧ x.Match' = W64 0))

/-- What the model's histories satisfy, for the watch check: the stores' items carry
revisions from 1 to the store's own, and no annotation; a change's new object carries the change's
revision; fewer than `2^63` revisions (see the file header). -/
def HistWf (x : Input) (hs : List GSt) : Prop :=
  hs.length < 2 ^ 63 ∧
  (∀ r it, r ≤ hs.length → it ∈ (histN hs r).items →
    1 ≤ uint.nat it.obj'.ResourceVersion' ∧ uint.nat it.obj'.ResourceVersion' ≤ r ∧
    it.obj'.Annotated' = false) ∧
  (∀ r e, evAtL x hs r = some e → uint.nat e.o.ResourceVersion' = r ∧ e.o.Annotated' = false)

/-- An event `encodeWEvents` encodes faithfully: its type is a byte, its object's fields fit, and
its object's encoding is shorter than `2^63`. -/
def WEvOk (e : WEv) : Prop := e.t < 256 ∧ fitsD e.o ∧ (encodeWith tagV1 e.o).length < 2 ^ 63

/-! ## The encoding round trip -/

theorem encWEvL_eq (e : WEv) : encWEvL e =
    W8 (e.t : Int) :: (if e.o.Annotated' then W8 1 else W8 0) ::
      (rvBytes e.o.ResourceVersion' ++ (rvBytes (W64 ((encodeWith tagV1 e.o).length : Int)) ++
        encodeWith tagV1 e.o)) := by
  simp [encWEvL, List.append_assoc]

theorem decWEventsL_cons (e : WEv) (rest : GoString) (he : WEvOk e) :
    decWEventsL (encWEvL e ++ rest) = (decWEventsL rest).map (e :: ·) := by
  obtain ⟨ht, hf, hl⟩ := he
  have hlen : (W64 ((encodeWith tagV1 e.o).length : Int)).toNat = (encodeWith tagV1 e.o).length := by
    simp only [W64, BitVec.toNat_ofInt]; omega
  rw [decWEventsL, encWEvL_eq]
  have hne : ¬ (W8 (e.t : Int) :: (if e.o.Annotated' then W8 1 else W8 0) ::
      (rvBytes e.o.ResourceVersion' ++ (rvBytes (W64 ((encodeWith tagV1 e.o).length : Int)) ++
        encodeWith tagV1 e.o)) ++ rest) = [] := by simp
  rw [dif_neg hne]
  have hlt : ¬ (W8 (e.t : Int) :: (if e.o.Annotated' then W8 1 else W8 0) ::
      (rvBytes e.o.ResourceVersion' ++ (rvBytes (W64 ((encodeWith tagV1 e.o).length : Int)) ++
        encodeWith tagV1 e.o)) ++ rest).length < 18 := by
    simp [rvBytes_length]; omega
  rw [if_neg hlt]
  simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.append_assoc]
  rw [List.drop_left' (rvBytes_length _), List.take_left' (rvBytes_length _), bytesBE_rvBytes, hlen]
  rw [show (List.drop 16 (rvBytes e.o.ResourceVersion' ++
      (rvBytes (W64 ((encodeWith tagV1 e.o).length : Int)) ++ (encodeWith tagV1 e.o ++ rest)))) =
      encodeWith tagV1 e.o ++ rest by
    rw [show 16 = 8 + 8 from rfl, ← List.drop_drop, List.drop_left' (rvBytes_length _),
      List.drop_left' (rvBytes_length _)]]
  rw [if_neg (by simp), List.take_left' rfl, decodeD_encode tagV1 (.inl rfl) e.o hf, List.drop_left' rfl]
  simp only [Option.map]
  cases decWEventsL rest with
  | none => rfl
  | some r =>
    simp only [List.headD_cons, List.take_left' (rvBytes_length _), bytesBE_rvBytes]
    have h1 : (W8 (e.t : Int)).toNat = e.t := by
      simp only [W8, BitVec.toNat_ofInt]; omega
    rw [h1]
    unfold withRvAnn
    cases e with | mk t o =>
    cases o with | mk a b c d f g rv ann =>
    cases ann <;> simp

/-- **`decodeWEvents` inverts `encodeWEvents`** on events it encodes faithfully. -/
theorem decWEventsL_enc (evs : List WEv) (h : ∀ e ∈ evs, WEvOk e) :
    decWEventsL (encWEventsL evs) = some evs := by
  induction evs with
  | nil => simp [encWEventsL, decWEventsL]
  | cons e evs ih =>
    simp only [encWEventsL, List.map_cons, List.flatten_cons] at ih ⊢
    rw [decWEventsL_cons e _ (h e (by simp)), ih (fun e' he' => h e' (by simp [he']))]
    rfl

/-! ## Events in a range of revisions -/

theorem toEventL_t {x : Input} {ch : Chg} {e : WEv} (h : toEventL x ch = some e) : e.t ≤ 2 := by
  unfold toEventL at h
  simp only at h
  split at h
  · rcases Option.map_eq_some_iff.1 h with ⟨o, -, rfl⟩; simp
  · split at h
    · rcases Option.map_eq_some_iff.1 h with ⟨o, -, rfl⟩; simp
    · split at h
      · rcases Option.map_eq_some_iff.1 h with ⟨o, -, rfl⟩; simp
      · cases h

theorem evAtL_t {x : Input} {hs : List GSt} {r : Nat} {e : WEv} (h : evAtL x hs r = some e) :
    e.t ≤ 2 := by
  unfold evAtL at h
  split at h
  · obtain ⟨ch, -, hc⟩ := Option.bind_eq_some_iff.1 h
    split at hc
    · exact toEventL_t hc
    · cases hc
  · cases h

theorem eventsInL_eq_nil (x : Input) (hs : List GSt) (a b : Nat)
    (h : ∀ r, a ≤ r → r < b → evAtL x hs r = none) : eventsInL x hs a b = [] := by
  unfold eventsInL
  rw [List.filterMap_eq_nil_iff]
  intro r hr
  rw [List.mem_range'_1] at hr
  exact h r hr.1 (by omega)

theorem eventsInL_split (x : Input) (hs : List GSt) (a k b : Nat) (h1 : a ≤ k) (h2 : k ≤ b) :
    eventsInL x hs a b = eventsInL x hs a k ++ eventsInL x hs k b := by
  unfold eventsInL
  rw [← List.filterMap_append]
  congr 1
  have := @List.range'_append_1 a (k - a) (b - k)
  rw [show a + (k - a) = k by omega, show k - a + (b - k) = b - a by omega] at this
  exact this.symm

theorem eventsInL_one (x : Input) (hs : List GSt) (r : Nat) :
    eventsInL x hs r (r + 1) = (evAtL x hs r).toList := by
  unfold eventsInL
  rw [show r + 1 - r = 1 by omega]
  simp only [List.range'_succ, List.range'_zero, List.filterMap_cons, List.filterMap_nil]
  cases evAtL x hs r <;> rfl

/-! ## A tail's revisions -/

/-- A tail's last cursor: the revision of its last element, or `c` for none. -/
def lastCur (c : Nat) : List WEv → Nat
  | [] => c
  | e :: rest => lastCur (uint.nat e.o.ResourceVersion') rest

section tail
variable {x : Input} {hs : List GSt}

/-- A tail's elements: an event at a revision past the cursor, a bookmark at or past it, all at
most the tail's last cursor, which is at most the history's length. -/
theorem TailOk.bounds (hwf : HistWf x hs) {c : Nat} {es : List WEv} (ht : TailOk x hs c es) :
    c ≤ lastCur c es ∧ (c ≤ hs.length → lastCur c es ≤ hs.length) ∧
    ∀ e ∈ es, (e.t = 3 ∨ c < uint.nat e.o.ResourceVersion') ∧
      c ≤ uint.nat e.o.ResourceVersion' ∧ uint.nat e.o.ResourceVersion' ≤ lastCur c es ∧
      uint.nat e.o.ResourceVersion' ≤ hs.length := by
  induction ht with
  | nil c => exact ⟨Nat.le_refl _, fun h => h, fun e he => by cases he⟩
  | ev c r e rest hcr hr _ hev _ ih =>
    have hrv := (hwf.2.2 r e hev).1
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [lastCur, hrv] at h1 h2 h3 ⊢
    refine ⟨by omega, fun _ => h2 hr, ?_⟩
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · rw [hrv]; exact ⟨.inr hcr, by omega, h1, hr⟩
    · obtain ⟨a, b, c', d⟩ := h3 e' he'
      exact ⟨a.imp id (by omega), by omega, c', d⟩
  | bm c p o rest hcp hp hrv _ _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [lastCur, hrv] at h1 h2 h3 ⊢
    refine ⟨by omega, fun _ => h2 hp, ?_⟩
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · simp only [hrv]; exact ⟨.inl trivial, hcp, h1, hp⟩
    · obtain ⟨a, b, c', d⟩ := h3 e' he'
      exact ⟨a.imp id (by omega), by omega, c', d⟩

/-- **A tail's events are exactly the history's events** over any range from past the cursor to
at most past its last cursor that holds them. -/
theorem TailOk.eventsIn (hwf : HistWf x hs) {c : Nat} {es : List WEv} (ht : TailOk x hs c es) :
    ∀ lo hi, c + 1 ≤ lo → (∀ e ∈ es, e.t ≠ 3 → lo ≤ uint.nat e.o.ResourceVersion') →
      (∀ e ∈ es, e.t ≠ 3 → uint.nat e.o.ResourceVersion' < hi) → hi ≤ lastCur c es + 1 →
      eventsInL x hs lo hi = es.filter (fun e => e.t ≠ 3) := by
  induction ht with
  | nil c =>
    intro lo hi hlo _ _ hhi
    simp only [lastCur] at hhi
    rw [eventsInL_eq_nil x hs lo hi (fun r h1 h2 => by omega)]; rfl
  | ev c r e rest hcr hr hgap hev ht ih =>
    intro lo hi hlo hle hlt hhi
    have hrv := (hwf.2.2 r e hev).1
    have het : e.t ≠ 3 := by have := evAtL_t hev; omega
    have hlor : lo ≤ r := by rw [← hrv]; exact hle e (by simp) het
    have hrhi : r < hi := by rw [← hrv]; exact hlt e (by simp) het
    have hb := TailOk.bounds hwf ht
    rw [eventsInL_split x hs lo r hi hlor (by omega),
      eventsInL_split x hs r (r + 1) hi (by omega) (by omega),
      eventsInL_eq_nil x hs lo r (fun r' h1 h2 => hgap r' (by omega) h2), eventsInL_one, hev,
      ih (r + 1) hi (Nat.le_refl _)
        (fun e' he' ht' => by have := (hb.2.2 e' he').1; omega)
        (fun e' he' ht' => hlt e' (by simp [he']) ht')
        (by simp only [lastCur, hrv] at hhi; exact hhi)]
    simp [List.filter_cons, het]
  | bm c p o rest hcp hp hrv hgap ht ih =>
    intro lo hi hlo hle hlt hhi
    have hb := TailOk.bounds hwf ht
    simp only [List.filter_cons, show (3 : Nat) ≠ 3 ↔ False from by simp, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    simp only [lastCur, hrv] at hhi
    by_cases hlp : lo ≤ p
    · by_cases hhp : p + 1 ≤ hi
      · rw [eventsInL_split x hs lo (p + 1) hi (by omega) hhp,
          eventsInL_eq_nil x hs lo (p + 1) (fun r' h1 h2 => hgap r' (by omega) (by omega)),
          ih (p + 1) hi (Nat.le_refl _)
            (fun e' he' ht' => by have := (hb.2.2 e' he').1; omega)
            (fun e' he' ht' => hlt e' (by simp [he']) ht') hhi]
        rfl
      · rw [eventsInL_eq_nil x hs lo hi (fun r' h1 h2 => hgap r' (by omega) (by omega))]
        symm
        rw [List.filter_eq_nil_iff]
        intro e' he' ht'
        have h1 := (hb.2.2 e' he').1
        have h2 := hlt e' (by simp [he']) (by simpa using ht')
        simp only [decide_eq_true_eq] at ht'
        omega
    · exact ih lo hi (by omega) (fun e' he' ht' => hle e' (by simp [he']) ht')
        (fun e' he' ht' => hlt e' (by simp [he']) ht') hhi

end tail

/-! ## The events' revision range -/

theorem evRange_foldl_some (es : List WEv) (lo hi : Nat) :
    ∃ lo' hi', es.foldl evRStep (some (lo, hi)) = some (lo', hi') ∧
      lo' ≤ lo ∧ (∀ e ∈ es, lo' ≤ evLo e) ∧ (lo' = lo ∨ ∃ e ∈ es, lo' = evLo e) ∧
      hi ≤ hi' ∧ (∀ e ∈ es, evHi e ≤ hi') ∧ (hi' = hi ∨ ∃ e ∈ es, hi' = evHi e) := by
  induction es generalizing lo hi with
  | nil => exact ⟨lo, hi, rfl, Nat.le_refl _, by simp, .inl rfl, Nat.le_refl _, by simp, .inl rfl⟩
  | cons e es ih =>
    obtain ⟨lo', hi', hf, h1, h2, h3, h4, h5, h6⟩ := ih (min (evLo e) lo) (max (evHi e) hi)
    refine ⟨lo', hi', hf, Nat.le_trans h1 (Nat.min_le_right _ _), ?_, ?_,
      Nat.le_trans (Nat.le_max_right _ _) h4, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact Nat.le_trans h1 (Nat.min_le_left _ _)
      · exact h2 e' he'
    · rcases h3 with h3 | ⟨e', he', h3⟩
      · by_cases hm : evLo e ≤ lo
        · exact .inr ⟨e, by simp, h3.trans (Nat.min_eq_left hm)⟩
        · exact .inl (h3.trans (Nat.min_eq_right (by omega)))
      · exact .inr ⟨e', by simp [he'], h3⟩
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact Nat.le_trans (Nat.le_max_left _ _) h4
      · exact h5 e' he'
    · rcases h6 with h6 | ⟨e', he', h6⟩
      · by_cases hm : hi ≤ evHi e
        · exact .inr ⟨e, by simp, h6.trans (Nat.max_eq_left hm)⟩
        · exact .inl (h6.trans (Nat.max_eq_right (by omega)))
      · exact .inr ⟨e', by simp [he'], h6⟩

/-- A non-empty list's range: its least `evLo`, attained, and its greatest `evHi`, attained. -/
theorem evRangeL_cons (e : WEv) (es : List WEv) :
    ∃ lo hi, evRangeL (e :: es) = some (lo, hi) ∧
      (∀ e' ∈ e :: es, lo ≤ evLo e') ∧ (∃ e' ∈ e :: es, lo = evLo e') ∧
      (∀ e' ∈ e :: es, evHi e' ≤ hi) ∧ (∃ e' ∈ e :: es, hi = evHi e') := by
  obtain ⟨lo', hi', hf, h1, h2, h3, h4, h5, h6⟩ := evRange_foldl_some es (evLo e) (evHi e)
  refine ⟨lo', hi', hf, ?_, ?_, ?_, ?_⟩
  · intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h1
    · exact h2 e' he'
  · rcases h3 with h3 | ⟨e', he', h3⟩
    · exact ⟨e, by simp, h3⟩
    · exact ⟨e', by simp [he'], h3⟩
  · intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h4
    · exact h5 e' he'
  · rcases h6 with h6 | ⟨e', he', h6⟩
    · exact ⟨e, by simp, h6⟩
    · exact ⟨e', by simp [he'], h6⟩

theorem evRangeL_nil : evRangeL [] = none := rfl

/-! ## The bookmarks -/

theorem bmStepL_none_foldl (es : List WEv) : es.foldl bmStepL none = none := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa [List.foldl_cons, bmStepL] using ih

section tail2
variable {x : Input} {hs : List GSt}

/-- A tail passes `validateBookmarks` from any state no later than its cursor. -/
theorem TailOk.bookmarks (hwf : HistWf x hs) {c : Nat} {es : List WEv} (ht : TailOk x hs c es)
    (hna : NoAnn es) : ∀ lb le ann, lb ≤ c → le ≤ c →
      (es.foldl bmStepL (some (lb, le, ann))).isSome := by
  induction ht with
  | nil c => intros; rfl
  | ev c r e rest hcr hr _ hev _ ih =>
    intro lb le ann hlb hle
    have hrv := (hwf.2.2 r e hev).1
    have het : e.t ≠ 3 := by have := evAtL_t hev; omega
    simp only [List.foldl_cons, bmStepL, hrv, het, ↓reduceIte, show ¬ r ≤ lb by omega]
    exact ih (fun e' he' => hna e' (by simp [he'])) lb (max le r) ann (by omega) (by omega)
  | bm c p o rest hcp hp hrv _ _ ih =>
    intro lb le ann hlb hle
    have hoa : o.Annotated' = false := hna ⟨3, o⟩ (by simp) rfl
    simp only [List.foldl_cons, bmStepL, hrv, ↓reduceIte, hoa, Bool.false_eq_true,
      show ¬ (p < lb ∨ p < le) by omega]
    exact ih (fun e' he' => hna e' (by simp [he'])) p le ann (Nat.le_refl _) (by omega)

end tail2

/-- Added events with revisions from 1 to `r0` pass `validateBookmarks` from the start, ending at
a state with no bookmark and the last event no later than `r0`. -/
theorem bm_init (init : List WEv) (r0 : Nat)
    (hi : ∀ e ∈ init, e.t = 0 ∧ 1 ≤ uint.nat e.o.ResourceVersion' ∧ uint.nat e.o.ResourceVersion' ≤ r0) :
    ∀ le, le ≤ r0 → ∃ le', le' ≤ r0 ∧ init.foldl bmStepL (some (0, le, false)) = some (0, le', false) := by
  induction init with
  | nil => intro le hle; exact ⟨le, hle, rfl⟩
  | cons e init ih =>
    intro le hle
    obtain ⟨h0, h1, h2⟩ := hi e (by simp)
    simp only [List.foldl_cons, bmStepL, h0, show (0 : Nat) ≠ 3 by decide, ↓reduceIte,
      show ¬ uint.nat e.o.ResourceVersion' ≤ 0 by omega]
    exact ih (fun e' he' => hi e' (by simp [he'])) _ (by omega)

/-! ## The reliable window -/

section tail3
variable {x : Input} {hs : List GSt}

/-- **`reliableOk` accepts a tail** from the cursor `c`, for the driver's requests: a NotOlderThan
request from at most `c` (or none), or a legacy one from exactly `c`. -/
theorem TailOk.reliable (hwf : HistWf x hs) {c : Nat} {es : List WEv} (ht : TailOk x hs c es)
    (hc : c ≤ hs.length) (req : Nat) (h : HSt) (hh : h.hist = hs)
    (hrv : uint.nat h.st.rv = hs.length)
    (hmode : (x.Match' = W64 1 ∧ (0 < req → req ≤ c)) ∨ (x.Match' = W64 0 ∧ 0 < req ∧ c = req)) :
    reliableOkL x req es h = true := by
  have hb := TailOk.bounds hwf ht
  unfold reliableOkL
  cases es with
  | nil => rw [evRangeL_nil]
  | cons e es =>
    obtain ⟨lo0, hi, hr, hlo1, ⟨elo, helo, hlo2⟩, hhi1, ⟨ehi, hehi, hhi2⟩⟩ := evRangeL_cons e es
    rw [hr]
    simp only
    have hm2 : x.Match' ≠ W64 2 := by
      rcases hmode with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> decide
    have hlo0 : c + 1 ≤ lo0 := by
      obtain ⟨hb1, hb2, -, -⟩ := hb.2.2 elo helo
      rw [hlo2]; unfold evLo
      split
      · omega
      · rcases hb1 with h | h
        · contradiction
        · omega
    have hhi : hi ≤ lastCur c (e :: es) + 1 := by
      obtain ⟨-, -, hb3, -⟩ := hb.2.2 ehi hehi
      rw [hhi2]; unfold evHi; split <;> omega
    have hlast := hb.2.1 hc
    rw [if_neg (fun h => hm2 h.1), if_neg (by omega), hh]
    have hlo : (if x.Match' = W64 1 then (if 0 < req then max lo0 (req + 1) else lo0)
        else if 0 < req then req + 1 else lo0) = (if x.Match' = W64 1 then lo0 else c + 1) := by
      rcases hmode with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · rw [if_pos h1, if_pos h1]
        split
        · have := h2 ‹_›; exact Nat.max_eq_left (by omega)
        · rfl
      · have h1' : x.Match' ≠ W64 1 := by rw [h1]; decide
        rw [if_neg h1', if_neg h1', if_pos h2, h3]
    rw [hlo]
    have hev : ∀ lo, c + 1 ≤ lo → (∀ e' ∈ e :: es, e'.t ≠ 3 → lo ≤ uint.nat e'.o.ResourceVersion') →
        evsEqL (eventsInL x hs lo hi) ((e :: es).filter fun e => e.t ≠ 3) = true := by
      intro lo h1 h2
      rw [TailOk.eventsIn hwf ht lo hi h1 h2
        (fun e' he' ht' => by have := hhi1 e' he'; unfold evHi at this; simp [ht'] at this; omega)
        hhi]
      simp [evsEqL]
    split
    · exact hev lo0 hlo0 (fun e' he' ht' => by have := hlo1 e' he'; unfold evLo at this; simp [ht'] at this; omega)
    · exact hev (c + 1) (Nat.le_refl _) (fun e' he' ht' => by
        have := (hb.2.2 e' he').1; rcases this with h | h
        · exact absurd h ht'
        · omega)

end tail3

end go

end k8s_etcd3
end EtcdGrove
end Perennial
