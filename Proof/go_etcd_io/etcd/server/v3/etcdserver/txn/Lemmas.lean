/-
The pure core of the verification of etcd's `server/v3/etcdserver/txn` package (unit 0b):
**the index answers the state.** Lean-first (no Rocq counterpart); the plan's "The index
answers the state", `notes/STATUS.md`, "The server's txn package".

mvcc's range reads are stated over the index (`rangeAnswers`, `rangeTaken`, `rangeTotal`,
`delKeys`, `Hist.lean`/`BucketLemmas.lean`); the txn package's results are stated over the
client model's state (`rangeIn`, `rangeSel`, `putKv`, the delete's filter, `InvEtcdTxn.lean`).
This file links the two, for a well-formed log (`LogOk`):

* `rangeAnswers_stateAt`: the answers of a range read at revision `r` are, one for one and in
  key order, the key-values of `stateAt log r` in the range (`srvSel`), each with its mod
  revision, create revision and version (`AnsKv`); corollaries for the keys, the count, the
  limit (`rangeTaken_stateAt`, `rangeTotal_stateAt`) and the keys a delete removes
  (`delKeys_eq`, `applyChanges_delKeys`);
* the range's end key: the server's `(endNil, e)` against the client's `rangeEnd`
  (`srvEnd`, `srvInRange_srvEnd`): `[]` is the one key, `[0]` (`mkGteRange` makes it an empty,
  non-nil slice) every key from `k` on, else `[k, rangeEnd)`;
* the model's changes are the client's operations (`applyChange_put`, `applyChanges_dels`);
* the index's history determines a log's *shape* (`logShape`: each revision's keys and
  whether each change is a delete), not its values (`histOf_prefix_logShape`): what the
  certificates can pin (`SoleWriter.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open mvcc

/-! ## The hypotheses -/

/-- A log the model's main theorem applies to: well formed (`LogWf`), with its length and each
revision's change count below `2 ^ 63` (`kiGet_indexOf`'s hypotheses). `idxCert`'s pure part
(`LogWf' log ∧ log.length < 2 ^ 63 ∧ …`) gives it for a non-empty log (`LogOk.of_cert`). -/
structure LogOk (log : Log) : Prop where
  wf : LogWf log
  len : log.length < 2 ^ 63
  cs : ∀ cs ∈ log, cs.length < 2 ^ 63

/-- `LogOk` from `idxCert`'s pure part, for a non-empty log. -/
theorem LogOk.of_cert {log : Log}
    (h : LogWf' log ∧ log.length < 2 ^ 63 ∧ ∀ cs ∈ log, cs.length < 2 ^ 63) (hne : log ≠ []) :
    LogOk log :=
  ⟨LogWf.of_wf' h.1 hne, h.2.1, h.2.2⟩

/-! ## The server's range -/

/-- A key is in a range of mvcc's reads: the one key `k` if the end key is `nil` (`endNil`),
else `[k, e)`, with no upper bound if `e` is empty (`mvcc.inRange`: `unsafeVisit`'s
`len(end) > 0` test). -/
def srvInRange (endNil : Bool) (k e key : GoString) : Bool :=
  if endNil then decide (key = k) else mvcc.inRange k e key

/-- The key-values of a state in a range of mvcc's reads, in the state's (key) order. -/
def srvSel (s : List EtcdKv) (endNil : Bool) (k e : GoString) : List EtcdKv :=
  s.filter fun v => srvInRange endNil k e v.key

/-- An answer `(key, (mod, created, ver))` of the index stands for the key-value `v` of the
state `st` (at the answer's revision of `log`): `v` is `st`'s key-value of `key`, its mod
revision, create revision and version are the answer's (the mains of the two revisions), and
the bucket has `v` at the mod revision (`BucketHas`: the change at `mod`, sub-revision
included, wrote it). The created revision's sub-revision is the sub-revision of the first put
of the key's generation; no result needs it, and it is not stated. -/
def AnsKv (log : Log) (st : List EtcdKv) (a : GoString × Rev × Rev × w64) (v : EtcdKv) : Prop :=
  findKey a.1 st = some v ∧ v.modRev = a.2.1.main ∧ v.createRev = a.2.2.1.main ∧
    v.version = a.2.2.2 ∧ BucketHas log a.2.1 v

theorem AnsKv.key {log : Log} {st : List EtcdKv} {a : GoString × Rev × Rev × w64} {v : EtcdKv}
    (h : AnsKv log st a v) : v.key = a.1 :=
  findKey_key h.1

/-! ## Sorted states: `findKey` -/

/-- In a state sorted by key, a member is what its key finds. -/
theorem findKey_of_mem_sorted : ∀ {s : List EtcdKv}, s.Pairwise etcdKvLess → ∀ {v : EtcdKv},
    v ∈ s → findKey v.key s = some v
  | [], _, _, h => absurd h List.not_mem_nil
  | w :: ws, hs, v, hv => by
    rw [List.pairwise_cons] at hs
    rw [findKey_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · simp
    · have hlt : etcdKvLess w v := hs.1 v hv
      have hne : w.key ≠ v.key := fun h => by
        unfold etcdKvLess at hlt; rw [h] at hlt; exact goStringLt_irrefl _ hlt
      simp only [hne, ↓reduceIte]
      exact findKey_of_mem_sorted hs.2 hv

/-- Filtering by a key predicate the key passes does not change what the key finds. -/
theorem findKey_filter_of (p : GoString → Bool) (key : GoString) (hp : p key = true) :
    ∀ s : List EtcdKv, findKey key (s.filter fun v => p v.key) = findKey key s
  | [] => rfl
  | w :: ws => by
    rw [List.filter_cons]
    by_cases hw : w.key = key
    · have hpw : p w.key = true := by rw [hw]; exact hp
      simp only [hw, hp, ↓reduceIte, findKey_cons]
    · have ih := findKey_filter_of p key hp ws
      split <;> simp only [findKey_cons, hw, ↓reduceIte, ih]

/-- In a sorted state, the key-values with key `k` are what `k` finds. -/
theorem filter_key_eq (k : GoString) : ∀ {s : List EtcdKv}, s.Pairwise etcdKvLess →
    s.filter (fun v => decide (v.key = k)) = (findKey k s).toList
  | [], _ => rfl
  | w :: ws, hs => by
    rw [List.pairwise_cons] at hs
    rw [List.filter_cons, findKey_cons]
    by_cases hw : w.key = k
    · simp only [hw, decide_true, ↓reduceIte, Option.toList_some, List.cons.injEq, true_and]
      rw [List.filter_eq_nil_iff]
      intro v hv hvk
      have hlt : etcdKvLess w v := hs.1 v hv
      unfold etcdKvLess at hlt
      rw [hw, of_decide_eq_true hvk] at hlt
      exact goStringLt_irrefl _ hlt
    · simp only [hw, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact filter_key_eq k hs.2

/-! ## Answers by key, against a sorted state -/

/-- `Forall₂` maps to equal lists under functions the relation identifies. -/
theorem forall2_map_eq {α β γ : Type} {R : α → β → Prop} (f : α → γ) (g : β → γ)
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {A : List α} {B : List β}, List.Forall₂ R A B → A.map f = B.map g
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    rw [List.map_cons, List.map_cons, hfg _ _ h, forall2_map_eq f g hfg t]

theorem forall2_length {α β : Type} {R : α → β → Prop} :
    ∀ {A : List α} {B : List β}, List.Forall₂ R A B → A.length = B.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by rw [List.length_cons, List.length_cons, forall2_length t]

theorem forall2_take {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) {A : List α} {B : List β}, List.Forall₂ R A B → List.Forall₂ R (A.take n) (B.take n)
  | 0, _, _, _ => by simp only [List.take_zero]; exact .nil
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons h t => by
    simp only [List.take_succ_cons]; exact .cons h (forall2_take n t)

theorem forall2_takeLimit {α β : Type} {R : α → β → Prop} (lim : Option Nat) {A : List α}
    {B : List β} (h : List.Forall₂ R A B) : List.Forall₂ R (takeLimit lim A) (takeLimit lim B) := by
  cases lim with
  | none => exact h
  | some n => exact forall2_take n h

theorem forall2_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {A : List α} {B : List β}, List.Forall₂ R A B → ∀ a ∈ A, ∃ b ∈ B, R a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons h t, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨b, hb, hr⟩ := forall2_mem_left t a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-- **Answers key by key.** A sorted list of keys `T` covering the sorted state `S`'s keys, and
an answer function `f` that answers a key exactly when `S` has it (with an answer related to
its key-value): the answers of `T`, in order, are `S`'s key-values one for one. -/
theorem forall2_filterMap_keys {α : Type} (R : α → EtcdKv → Prop) (f : GoString → Option α) :
    ∀ (T : List GoString) (S : List EtcdKv), T.Pairwise go.GoStringLt → S.Pairwise etcdKvLess →
    (∀ key ∈ T, findKey key S = none → f key = none) →
    (∀ key ∈ T, ∀ v, findKey key S = some v → ∃ a, f key = some a ∧ R a v) →
    (∀ v ∈ S, v.key ∈ T) →
    List.Forall₂ R (T.filterMap f) S
  | [], S, _, _, _, _, h2 => by
    cases S with
    | nil => exact List.Forall₂.nil
    | cons v _ => exact absurd (h2 v List.mem_cons_self) List.not_mem_nil
  | t :: T, S, hT, hS, hn, hs, h2 => by
    rw [List.pairwise_cons] at hT
    rw [List.filterMap_cons]
    cases hf : findKey t S with
    | none =>
      rw [hn t List.mem_cons_self hf]
      refine forall2_filterMap_keys R f T S hT.2 hS (fun key hk => hn key (List.mem_cons_of_mem _ hk))
        (fun key hk => hs key (List.mem_cons_of_mem _ hk)) ?_
      intro v hv
      rcases List.mem_cons.1 (h2 v hv) with h | h
      · exfalso
        have := findKey_of_mem_sorted hS hv
        rw [h, hf] at this
        cases this
      · exact h
    | some v =>
      obtain ⟨a, ha, hR⟩ := hs t List.mem_cons_self v hf
      rw [ha]
      cases S with
      | nil => rw [findKey_nil] at hf; cases hf
      | cons w S' =>
        have hS' := List.pairwise_cons.1 hS
        have hvk : v.key = t := findKey_key hf
        have hvmem : v ∈ w :: S' := by
          unfold findKey at hf; exact List.mem_of_find?_eq_some hf
        have hwk : w.key = t := by
          rcases List.mem_cons.1 (h2 w List.mem_cons_self) with h | h
          · exact h
          · exfalso
            have htw : go.GoStringLt t w.key := hT.1 _ h
            rcases List.mem_cons.1 hvmem with hv | hv
            · subst hv; rw [hvk] at htw; exact goStringLt_irrefl _ htw
            · have hwv : go.GoStringLt w.key v.key := hS'.1 v hv
              rw [hvk] at hwv
              exact goStringLt_irrefl _ (goStringLt_trans htw hwv)
        have hwv : w = v := by
          rw [findKey_cons, hwk] at hf
          simpa using hf
        subst hwv
        have hlt : ∀ key ∈ T, w.key ≠ key := fun key hk h => by
          have := hT.1 key hk; rw [← h, hwk] at this; exact goStringLt_irrefl _ this
        refine List.Forall₂.cons hR ?_
        apply forall2_filterMap_keys R f T S' hT.2 hS'.2
        · intro key hk hnone
          apply hn key (List.mem_cons_of_mem _ hk)
          rw [findKey_cons]; simp only [hlt key hk, ↓reduceIte]; exact hnone
        · intro key hk v' hv'
          apply hs key (List.mem_cons_of_mem _ hk)
          rw [findKey_cons]; simp only [hlt key hk, ↓reduceIte]; exact hv'
        · intro v' hv'
          rcases List.mem_cons.1 (h2 v' (List.mem_cons_of_mem _ hv')) with h | h
          · exfalso
            have hwv' : go.GoStringLt w.key v'.key := hS'.1 v' hv'
            rw [h, ← hwk] at hwv'
            exact goStringLt_irrefl _ hwv'
          · exact h

/-! ## The index answers the state -/

/-- The keys whose answers a range read collects, in key order: the one key, or the index's
keys in `[k, e)`. -/
def rangeKeys (log : Log) (endNil : Bool) (k e : GoString) : List GoString :=
  if endNil then [k] else ((indexOf (evsOf log)).map Prod.fst).filter (mvcc.inRange k e)

theorem rangeAnswers_eq_keys (log : Log) (endNil : Bool) (k e : GoString) (atRev : w64) :
    rangeAnswers log endNil k e atRev =
      (rangeKeys log endNil k e).filterMap fun key =>
        (kiGet (kiOfKey (evsOf log) key) atRev).map fun x => (key, x) := by
  cases endNil with
  | true =>
    rw [rangeAnswers_nil]
    unfold rangeKeys
    simp only [↓reduceIte, List.filterMap_cons, List.filterMap_nil]
    cases kiGet (kiOfKey (evsOf log) k) atRev <;> rfl
  | false =>
    unfold rangeAnswers rangeKeys
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [rangeAt_eq_keys _ (indexOf_sorted _)]
    simp only [kiAt_indexOf]

theorem rangeKeys_sorted (log : Log) (endNil : Bool) (k e : GoString) :
    (rangeKeys log endNil k e).Pairwise go.GoStringLt := by
  unfold rangeKeys
  cases endNil with
  | true => simp
  | false => exact (keys_sorted _).filter _

/-- What the index answers of a key at revision `r` matches the key's key-value in the state
(`kiGet_indexOf`, by key). -/
theorem kvMatch_key (log : Log) (hok : LogOk log) (key : GoString) (r : Nat) (hr : r < 2 ^ 63) :
    KvMatch log (kiGet (kiOfKey (evsOf log) key) (W64 r)) (findKey key (stateAt log r)) := by
  have := kiGet_indexOf log hok.len hok.cs hok.wf key r hr
  rwa [idxGet_indexOf_bind] at this

/-- **The index answers the state.** For a well-formed log, the answers of a range read at
revision `r` (`rangeAnswers`: the one key if `endNil`, else the keys in `[k, e)`, `e = []`
meaning no upper bound) are, one for one and in key order, the key-values of the state at `r`
in the range (`srvSel`), each with the answer's mod revision, create revision and version
(`AnsKv`). -/
theorem rangeAnswers_stateAt (log : Log) (hok : LogOk log) (endNil : Bool) (k e : GoString)
    (r : Nat) (hr : r < 2 ^ 63) :
    List.Forall₂ (AnsKv log (stateAt log r)) (rangeAnswers log endNil k e (W64 r))
      (srvSel (stateAt log r) endNil k e) := by
  rw [rangeAnswers_eq_keys]
  have hst := stateAt_sorted log r
  have hinT : ∀ key ∈ rangeKeys log endNil k e, srvInRange endNil k e key = true := by
    intro key hk
    unfold rangeKeys at hk
    unfold srvInRange
    cases endNil with
    | true => simp only [↓reduceIte, List.mem_singleton] at hk ⊢; simp [hk]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_filter] at hk ⊢
      exact hk.2
  have hfS : ∀ key ∈ rangeKeys log endNil k e,
      findKey key ((stateAt log r).filter fun v => srvInRange endNil k e v.key) =
        findKey key (stateAt log r) :=
    fun key hk => findKey_filter_of (srvInRange endNil k e) key (hinT key hk) _
  apply forall2_filterMap_keys _ _ _ _ (rangeKeys_sorted log endNil k e) (hst.filter _)
  · intro key hk hnone
    rw [hfS key hk] at hnone
    have hm := kvMatch_key log hok key r hr
    rw [hnone] at hm
    rw [KvMatch_none_right hm]
    rfl
  · intro key hk v hv
    rw [hfS key hk] at hv
    have hm := kvMatch_key log hok key r hr
    rw [hv] at hm
    cases hg : kiGet (kiOfKey (evsOf log) key) (W64 r) with
    | none => rw [hg] at hm; exact absurd hm id
    | some x =>
      obtain ⟨rev, created, ver⟩ := x
      rw [hg] at hm
      obtain ⟨h1, h2, h3, h4⟩ := hm
      exact ⟨(key, rev, created, ver), rfl, hv, h1, h2, h3, h4⟩
  · intro v hv
    unfold srvSel at hv
    rw [List.mem_filter] at hv
    have hfind := findKey_of_mem_sorted hst hv.1
    have hm := kvMatch_key log hok v.key r hr
    rw [hfind] at hm
    have hne : kiOfKey (evsOf log) v.key ≠ kiEmpty := by
      intro he
      rw [he, kiGet_kiEmpty] at hm
      exact hm
    unfold rangeKeys
    have hin := hv.2
    unfold srvInRange at hin
    cases endNil with
    | true =>
      simp only [↓reduceIte, decide_eq_true_eq] at hin ⊢
      exact List.mem_singleton.2 hin
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hin ⊢
      exact List.mem_filter.2 ⟨(mem_keys_iff _ _).2 hne, hin⟩

/-- The keys answered are the state's keys in the range. -/
theorem rangeAnswers_keys (log : Log) (hok : LogOk log) (endNil : Bool) (k e : GoString)
    (r : Nat) (hr : r < 2 ^ 63) :
    (rangeAnswers log endNil k e (W64 r)).map Prod.fst =
      (srvSel (stateAt log r) endNil k e).map EtcdKv.key :=
  forall2_map_eq Prod.fst EtcdKv.key (fun _ _ h => (AnsKv.key h).symm) (rangeAnswers_stateAt log hok endNil k e r hr)

/-- What each answer's key finds in the state, in order: the state's key-values in the range
(the `KVs` a range read fills, `rangeKvs`). -/
theorem rangeAnswers_findKey (log : Log) (hok : LogOk log) (endNil : Bool) (k e : GoString)
    (r : Nat) (hr : r < 2 ^ 63) :
    (rangeAnswers log endNil k e (W64 r)).map (fun a => findKey a.1 (stateAt log r)) =
      (srvSel (stateAt log r) endNil k e).map some :=
  forall2_map_eq (fun a => findKey a.1 (stateAt log r)) some (fun _ _ h => h.1) (rangeAnswers_stateAt log hok endNil k e r hr)

/-- As many answers as key-values in the range (a `CountOnly` read's count). -/
theorem rangeAnswers_length (log : Log) (hok : LogOk log) (endNil : Bool) (k e : GoString)
    (r : Nat) (hr : r < 2 ^ 63) :
    (rangeAnswers log endNil k e (W64 r)).length = (srvSel (stateAt log r) endNil k e).length :=
  forall2_length (rangeAnswers_stateAt log hok endNil k e r hr)

/-- `rangeAnswers_stateAt` at a word revision (`rangeOutcome`'s `rangeRev`, non-negative): the
state at its `sint.nat`. -/
theorem rangeAnswers_stateAt_w (log : Log) (hok : LogOk log) (endNil : Bool) (k e : GoString)
    (atRev : w64) (h0 : 0 ≤ sint.Z atRev) :
    List.Forall₂ (AnsKv log (stateAt log (sint.nat atRev))) (rangeAnswers log endNil k e atRev)
      (srvSel (stateAt log (sint.nat atRev)) endNil k e) := by
  have h := rangeAnswers_stateAt log hok endNil k e (sint.nat atRev) (by
    unfold sint.nat sint.Z at *; have := BitVec.toInt_lt (x := atRev); simp at this; omega)
  rwa [W64_sint_nat atRev h0] at h

/-- The last revision of a log of length `n` as a word (a read transaction's `rev`): its signed
value. -/
theorem lastRev_sint (n : Nat) (h0 : 0 < n) (h : n ≤ 2 ^ 63) :
    sint.Z (W64 ((n : Int) - 1)) = (n : Int) - 1 := by
  word

theorem lastRev_nat (n : Nat) (h0 : 0 < n) (h : n ≤ 2 ^ 63) :
    sint.nat (W64 ((n : Int) - 1)) = n - 1 := by
  have := lastRev_sint n h0 h
  unfold sint.nat; unfold sint.Z at this; rw [this]; omega

/-- A read at the last revision of a log reads the state after it. -/
theorem stateAt_lastRev (log : Log) (hne : log ≠ []) (h : log.length ≤ 2 ^ 63) :
    stateAt log (sint.nat (W64 ((log.length : Int) - 1))) = stateAfter log := by
  rw [lastRev_nat _ (List.length_pos_iff.2 hne) h, stateAt_last]

/-! ## The limit and the count -/

/-- A one-key read answers at most one key. -/
theorem srvSel_true_length_le (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (k e : GoString) :
    (srvSel s true k e).length ≤ 1 := by
  unfold srvSel srvInRange
  simp only [↓reduceIte]
  rw [filter_key_eq k hs]
  cases findKey k s <;> simp

/-- `rangeTaken` is the answers up to the limit, for both kinds of reads (a one-key read has at
most one answer, which a positive limit keeps). -/
theorem rangeTaken_eq (log : Log) (endNil : Bool) (k e : GoString) (atRev limit : w64) :
    rangeTaken log endNil k e atRev limit =
      takeLimit (limitOf limit) (rangeAnswers log endNil k e atRev) := by
  cases endNil with
  | false => rfl
  | true =>
    rw [rangeTaken_true]
    have hle := rangeAnswers_nil_length_le log k e atRev
    unfold limitOf
    by_cases hpos : 0 < sint.Z limit
    · simp only [hpos, ↓reduceIte, takeLimit]
      rw [List.take_of_length_le (by omega)]
    · simp only [hpos, ↓reduceIte, takeLimit]

/-- A non-positive limit (`0`: no limit) takes every answer. -/
theorem rangeTaken_nonpos (log : Log) (endNil : Bool) (k e : GoString) (atRev limit : w64)
    (h : sint.Z limit ≤ 0) :
    rangeTaken log endNil k e atRev limit = rangeAnswers log endNil k e atRev := by
  rw [rangeTaken_eq]
  unfold limitOf
  simp only [show ¬ (0 < sint.Z limit) by omega, ↓reduceIte]
  rfl

/-- A positive limit takes that many answers. -/
theorem rangeTaken_pos (log : Log) (endNil : Bool) (k e : GoString) (atRev limit : w64)
    (h : 0 < sint.Z limit) :
    rangeTaken log endNil k e atRev limit =
      (rangeAnswers log endNil k e atRev).take (sint.Z limit).toNat := by
  rw [rangeTaken_eq]
  unfold limitOf
  simp only [h, ↓reduceIte]
  rfl

/-- **The taken answers** are the state's key-values in the range, up to the limit. -/
theorem rangeTaken_stateAt (log : Log) (hok : LogOk log) (endNil : Bool) (k e : GoString)
    (r : Nat) (hr : r < 2 ^ 63) (limit : w64) :
    List.Forall₂ (AnsKv log (stateAt log r)) (rangeTaken log endNil k e (W64 r) limit)
      (takeLimit (limitOf limit) (srvSel (stateAt log r) endNil k e)) := by
  rw [rangeTaken_eq]
  exact forall2_takeLimit _ (rangeAnswers_stateAt log hok endNil k e r hr)

/-- **The count** a range read returns: the number of key-values in the range (`withTotal`),
or at most the limit. -/
theorem rangeTotal_stateAt (log : Log) (hok : LogOk log) (endNil : Bool) (k e : GoString)
    (r : Nat) (hr : r < 2 ^ 63) (limit : w64) (withTotal : Bool) :
    rangeTotal log endNil k e (W64 r) limit withTotal =
      totalOf (limitOf limit) withTotal (srvSel (stateAt log r) endNil k e).length := by
  rw [← rangeAnswers_length log hok endNil k e r hr]
  cases endNil with
  | false => rfl
  | true =>
    rw [rangeTotal_true]
    have hle := rangeAnswers_nil_length_le log k e (W64 r)
    unfold limitOf
    by_cases hpos : 0 < sint.Z limit
    · simp only [hpos, ↓reduceIte]
      cases withTotal
      · simp only [totalOf]; omega
      · rfl
    · simp only [hpos, ↓reduceIte]; cases withTotal <;> rfl

/-! ## The changes are the client's operations -/

/-- A put of the model is the client's `putKv`. -/
theorem applyChange_put (r : w64) (s : List EtcdKv) (k v : GoString) (l : w64) :
    applyChange r s (.put k v l) = putKv r k v l s := rfl

/-- A delete of the model removes the key. -/
theorem applyChange_del (r : w64) (s : List EtcdKv) (k : GoString) :
    applyChange r s (.del k) = s.filter (fun x => !decide (x.key = k)) := rfl

theorem applyChanges_nil (r : w64) (s : List EtcdKv) : applyChanges r s [] = s := rfl

theorem applyChanges_append (r : w64) (s : List EtcdKv) (cs cs' : List Change) :
    applyChanges r s (cs ++ cs') = applyChanges r (applyChanges r s cs) cs' := by
  unfold applyChanges; rw [List.foldl_append]

theorem applyChanges_cons (r : w64) (s : List EtcdKv) (c : Change) (cs : List Change) :
    applyChanges r s (c :: cs) = applyChanges r (applyChange r s c) cs := rfl

/-- Deleting keys one by one removes them. -/
theorem applyChanges_dels (r : w64) :
    ∀ (ks : List GoString) (s : List EtcdKv),
      applyChanges r s (ks.map .del) = s.filter (fun v => !decide (v.key ∈ ks))
  | [], s => by simp only [List.map_nil, applyChanges_nil, List.not_mem_nil, decide_false, Bool.not_false]; exact (List.filter_eq_self.2 (fun _ _ => rfl)).symm
  | k :: ks, s => by
    rw [List.map_cons, applyChanges_cons, applyChange_del, applyChanges_dels r ks, List.filter_filter]
    apply List.filter_congr
    intro v _
    by_cases h1 : v.key = k
    · simp [h1]
    · simp [h1]

/-- Deleting the keys of a state's selection leaves the rest of the state. -/
theorem applyChanges_dels_sel (r : w64) (s : List EtcdKv) (p : GoString → Bool) :
    applyChanges r s (((s.filter fun v => p v.key).map EtcdKv.key).map .del) =
      s.filter (fun v => !p v.key) := by
  rw [applyChanges_dels]
  apply List.filter_congr
  intro v hv
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · intro h
    rw [List.mem_map] at h
    obtain ⟨w, hw, hwk⟩ := h
    rw [List.mem_filter] at hw
    rw [← hwk]; exact hw.2
  · intro h
    exact List.mem_map.2 ⟨v, List.mem_filter.2 ⟨hv, h⟩, rfl⟩

/-- The state after a log with one more revision. -/
theorem stateAfter_snoc (log : Log) (cs : List Change) :
    stateAfter (log ++ [cs]) = applyChanges (W64 log.length) (stateAfter log) cs :=
  stateAfter_append log cs

/-! ## What `deleteRange` deletes -/

/-- **The keys a write transaction's `deleteRange` deletes** (`delKeys`) are the keys of the
state after the pending changes in the range, in key order. -/
theorem delKeys_eq (ilog : Log) (pend : List Change) (hok : LogOk (ilog ++ [pend]))
    (hne : ilog ≠ []) (endNil : Bool) (k e : GoString) :
    delKeys ilog pend endNil k e =
      (srvSel (applyChanges (W64 ilog.length) (stateAfter ilog) pend) endNil k e).map EtcdKv.key := by
  have hlt := writeRev_lt ilog pend hne
  unfold delKeys
  rw [rangeTaken_nonpos _ _ _ _ _ _ (by simp [sint.Z]),
    rangeAnswers_keys _ hok endNil k e (writeRev ilog pend) (by have := hok.len; omega),
    stateAt_writeRev ilog pend hne]

/-- **A range delete is the client's filter**: the pending state with the deleted keys' changes
appended is the pending state without the range. -/
theorem applyChanges_delKeys (ilog : Log) (pend : List Change) (hok : LogOk (ilog ++ [pend]))
    (hne : ilog ≠ []) (endNil : Bool) (k e : GoString) :
    applyChanges (W64 ilog.length) (stateAfter ilog)
        (pend ++ (delKeys ilog pend endNil k e).map .del) =
      (applyChanges (W64 ilog.length) (stateAfter ilog) pend).filter
        (fun v => !srvInRange endNil k e v.key) := by
  rw [applyChanges_append, delKeys_eq ilog pend hok hne]
  exact applyChanges_dels_sel _ _ _

/-- As many keys deleted as key-values in the range. -/
theorem delKeys_length (ilog : Log) (pend : List Change) (hok : LogOk (ilog ++ [pend]))
    (hne : ilog ≠ []) (endNil : Bool) (k e : GoString) :
    (delKeys ilog pend endNil k e).length =
      (srvSel (applyChanges (W64 ilog.length) (stateAfter ilog) pend) endNil k e).length := by
  rw [delKeys_eq ilog pend hok hne, List.length_map]

/-! ## The client's range: the end key -/

/-- The server's range for the client's `rangeEnd` (after the protobuf round trip and
`mkGteRange`): an empty `rangeEnd` is a `nil` end key (the one key); `[0]` ("every key from
`k` on") becomes an empty, non-nil slice, which mvcc reads as no upper bound; any other is the
end key itself. -/
def srvEnd (rangeEnd : GoString) : Bool × GoString :=
  if rangeEnd = [] then (true, [])
  else if rangeEnd = [W8 0] then (false, [])
  else (false, rangeEnd)

/-- **The bridge**: the server's range of `srvEnd rangeEnd` is the client's `inRange`. -/
theorem srvInRange_srvEnd (k rangeEnd key : GoString) :
    srvInRange (srvEnd rangeEnd).1 k (srvEnd rangeEnd).2 key = inRange k rangeEnd key := by
  by_cases h0 : rangeEnd = []
  · subst h0; simp [srvEnd, srvInRange, inRange]
  · by_cases h1 : rangeEnd = [W8 0]
    · subst h1; simp [srvEnd, srvInRange, inRange, mvcc.inRange]
    · simp only [srvEnd, srvInRange, inRange, mvcc.inRange, h0, h1, ↓reduceIte, Bool.false_eq_true,
        decide_false, Bool.false_or]

/-- The server's selection of `srvEnd o.base.rangeEnd` is the client's `rangeIn`. -/
theorem srvSel_srvEnd (s : List EtcdKv) (o : OpFull) :
    srvSel s (srvEnd o.base.rangeEnd).1 o.key (srvEnd o.base.rangeEnd).2 = rangeIn s o := by
  unfold srvSel rangeIn
  apply List.filter_congr
  intro v _
  exact srvInRange_srvEnd _ _ _

/-- A range delete of the client's `o`, on the server: the client's delete. -/
theorem applyChanges_delKeys_client (ilog : Log) (pend : List Change) (hok : LogOk (ilog ++ [pend]))
    (hne : ilog ≠ []) (o : OpFull) :
    applyChanges (W64 ilog.length) (stateAfter ilog)
        (pend ++ (delKeys ilog pend (srvEnd o.base.rangeEnd).1 o.key (srvEnd o.base.rangeEnd).2).map .del) =
      (applyChanges (W64 ilog.length) (stateAfter ilog) pend).filter
        (fun v => !inRange o.key o.base.rangeEnd v.key) := by
  rw [applyChanges_delKeys ilog pend hok hne]
  apply List.filter_congr
  intro v _
  rw [srvInRange_srvEnd]

/-! ## The index's history determines a log's shape -/

/-- What the index records of a change: its key and whether it is a delete. -/
def chShape (c : Change) : GoString × Bool := (c.key, c.isDel)

/-- A log's shape: each revision's changes' keys and kinds (not the values and leases). -/
def logShape (log : Log) : List (List (GoString × Bool)) := log.map (·.map chShape)

/-- An event's key and kind. -/
def evShape (e : Ev) : GoString × Bool := (e.key, e.tomb)

theorem evsOfRev_shape (i : Nat) (cs : List Change) :
    (evsOfRev i cs).map evShape = cs.map chShape := by
  unfold evsOfRev
  rw [List.map_map]
  have : (evShape ∘ fun p : Change × Nat =>
      ({ rev := ⟨W64 i, W64 p.2⟩, change := p.1 } : Ev)) = chShape ∘ Prod.fst := rfl
  rw [this, ← List.map_map, List.zipIdx_map_fst]

theorem histOfFrom_ne_commit_free (i : Nat) (cs : List Change) (log : Log) (X : List HistItem)
    (hX : ∀ x ∈ X, x ≠ HistItem.commit) : ¬ histOfFrom i (cs :: log) <+: X := by
  intro h
  rw [histOfFrom] at h
  have : HistItem.commit ∈ X := h.subset (by simp)
  exact hX _ this rfl

/-- A history prefix of another followed by events alone (no commit): the shapes are prefixes. -/
theorem histOfFrom_prefix_logShape (i : Nat) : ∀ (a b : Log) (X : List HistItem),
    (∀ x ∈ X, x ≠ HistItem.commit) → histOfFrom i a <+: histOfFrom i b ++ X →
    logShape a <+: logShape b
  | [], b, _, _, _ => by simp [logShape]
  | c :: a, [], X, hX, h => by
    rw [show histOfFrom i ([] : Log) = [] from rfl, List.nil_append] at h
    exact absurd h (histOfFrom_ne_commit_free i c a X hX)
  | c :: a, c' :: b, X, hX, h => by
    rw [histOfFrom, histOfFrom, List.append_assoc ((evsOfRev i c').map HistItem.ev ++ [HistItem.commit])] at h
    obtain ⟨hcc, hpre⟩ := prefix_commit_split _ _ _ _ (map_ev_ne_commit _) (map_ev_ne_commit _) h
    have hc := map_ev_injective _ _ hcc
    have hs : c.map chShape = c'.map chShape := by
      rw [← evsOfRev_shape i c, ← evsOfRev_shape i c', hc]
    have ih := histOfFrom_prefix_logShape (i + 1) a b X hX hpre
    unfold logShape at ih ⊢
    rw [List.map_cons, List.map_cons, hs]
    exact (List.cons_prefix_cons).2 ⟨rfl, ih⟩

/-- **The certificates' order is the shapes' order**: a committed log's history that is a
prefix of the index's history (`histShape ilog pend`) has its shape a prefix of `ilog`'s. -/
theorem histOf_prefix_shape_logShape (log ilog : Log) (pend : List Change)
    (h : histOf log <+: histShape ilog pend) : logShape log <+: logShape ilog :=
  histOfFrom_prefix_logShape 0 log ilog _ (map_ev_ne_commit _) h

/-- Two committed logs' histories, one a prefix of the other: their shapes are. -/
theorem histOf_prefix_logShape (a b : Log) (h : histOf a <+: histOf b) :
    logShape a <+: logShape b :=
  histOfFrom_prefix_logShape 0 a b [] (by simp) (by rw [List.append_nil]; exact h)

theorem logShape_length (log : Log) : (logShape log).length = log.length := by
  unfold logShape; rw [List.length_map]

/-- Shapes in prefix order with the same length are equal. -/
theorem logShape_eq_of_prefix {a b : Log} (h : logShape a <+: logShape b)
    (hlen : b.length ≤ a.length) : logShape a = logShape b :=
  h.eq_of_length (by
    have := h.length_le
    rw [logShape_length, logShape_length] at this ⊢
    omega)

end txn
end EtcdGrove
end Perennial
