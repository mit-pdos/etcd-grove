/-
The history laws of the server's log (unit 4 of the txn package): pure Lean, no Rocq
counterpart; `notes/STATUS.md`, "Unit 4: the history laws of the log".

The client's model of etcd (`InvEtcd.lean`, `InvEtcdTxn.lean`) rests on axioms about etcd's
history, stated over an abstract `etcdState r pfx s` ("etcd's state at revision `r`, restricted
to the prefix `pfx`, is `s`"): `etcdState_agree`, `etcdState_revs`, `etcdState_create_persist`,
`etcdState_modrev_det` and `etcdState_modrev_persist`. The server's model of the same history
is mvcc's log (`Model.lean`): `stateAt log r`, the changes of revisions `0, ..., r` applied in
order. This file proves that **every law holds of `stateAt`** (with `stateAtPfx`, its
restriction to a prefix, for `etcdState`'s `pfx`):

* `stateAt_revs` (`etcdState_revs`): positive create revision, create ≤ mod ≤ `r`, positive
  version. Needs revision 0 empty (`log[0]? = some []`, in `LogWf`) and **each revision writes a
  key at most once** (`NoDupKeysPerRev`): without it a revision's repeated puts of one key grow
  its version by more than one per revision, and a long enough log wraps the version (a word)
  to a non-positive signed value. The revision parts need neither (`stateAt_revInv`).
* `stateAt_create_persist`, `stateAt_modrev_persist`, `stateAt_modrev_det`: only
  `log.length < 2 ^ 63` (the revisions are words). In particular `modrev_det` does **not** need
  `NoDupKeysPerRev`: two puts of a key in one revision give one mod revision, but only the
  later record survives the revision (`modrev_persist` puts both records in the state at their
  mod revision, which holds one record per key).
* `etcdState_agree`: `stateAt` is a function (`stateAtPfx_agree`); `stateAtPfx_wf`: its states
  are what `EtcdStateWf` says (sorted keys, under the prefix); the four laws restated per prefix
  (`stateAtPfx_*`).
* `etcdReachedAt` has no pure law; its log analogue: a revision of the log keeps its state as
  the log grows (`stateAt_of_prefix`), which is what makes `etcdState` of a reached revision
  persistent knowledge.
* **A commit keeps the hypotheses** (`LogOk.snoc`, `NoDupKeysPerRev.snoc`): appending one
  revision `pend` keeps `LogOk` if its deletes are of keys present when they run
  (`DelsPresent`, `LogWf`'s condition); it keeps `NoDupKeysPerRev` iff its keys are distinct,
  which, for such a revision, is exactly etcd's check of a transaction's requests
  (`checkIntervals`, "duplicate key given in txn request"): **the put keys are distinct and none
  is also deleted** (`keys_nodup_iff_check`); two deletes of one key in a revision need a put
  of it between them.

**What this does and does not show.** The client's `etcdState_*` are axioms over an abstract
`etcdState`; these theorems show the server's log model *validates* them (each law holds of
`stateAt`), they do not discharge them: nothing here links `etcdState` to a log. The hypotheses
beyond `LogOk` (`NoDupKeysPerRev`) are what the client's axioms assume of the server.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open mvcc

/-! ## Words -/

theorem hl_nat_W64 (n : Nat) (h : n < 2 ^ 63) : uint.nat (W64 (n : Int)) = n := by word

theorem hl_sint_eq (x : w64) (h : uint.nat x < 2 ^ 63) : sint.Z x = (uint.nat x : Int) := by word

theorem hl_succ (x : w64) (h : uint.nat x < 2 ^ 63) : uint.nat (x + W64 1) = uint.nat x + 1 := by
  word

theorem hl_W64_ne (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (h : a ≠ b) :
    W64 (a : Int) ≠ W64 (b : Int) := by
  intro e; apply h; have := congrArg uint.nat e; rw [hl_nat_W64 a ha, hl_nat_W64 b hb] at this
  exact this

/-! ## The state at a revision, one revision at a time -/

theorem stateAt_zero (log : Log) (h : 0 < log.length) :
    stateAt log 0 = applyChanges (W64 0) [] log[0] := by
  unfold stateAt
  rw [List.take_add_one, List.take_zero, List.nil_append, List.getElem?_eq_getElem h,
    Option.toList_some]
  rfl

theorem stateAt_succ (log : Log) (j : Nat) (h : j + 1 < log.length) :
    stateAt log (j + 1) = applyChanges (W64 ((j + 1 : Nat) : Int)) (stateAt log j) log[j + 1] := by
  unfold stateAt
  rw [List.take_add_one (i := j + 1), List.getElem?_eq_getElem h, Option.toList_some,
    stateAfter_append, List.length_take, Nat.min_eq_left (by omega)]

/-- Revision 0 empty: the state at 0 is empty. -/
theorem stateAt_zero_nil (log : Log) (h : log[0]? = some []) : stateAt log 0 = [] := by
  have hl : 0 < log.length := (List.getElem?_eq_some_iff.1 h).1
  rw [stateAt_zero log hl]
  rw [List.getElem?_eq_getElem hl, Option.some.injEq] at h
  rw [h]; rfl

/-! ## What a change does to a member -/

/-- A member of the state after a put: an old member, or the put key's new record (an update
of its old record, or a new one created at `r`). -/
theorem mem_putKv {r : w64} {k val : GoString} {l : w64} {s : List EtcdKv} {v : EtcdKv}
    (h : v ∈ putKv r k val l s) :
    v ∈ s ∨ (v.key = k ∧ v.modRev = r ∧
      ((∃ w ∈ s, w.key = k ∧ v.createRev = w.createRev ∧ v.version = w.version + W64 1) ∨
       (v.createRev = r ∧ v.version = W64 1))) := by
  unfold putKv at h
  rcases btInsert_mem h with h | h
  · right
    cases hf : s.find? (fun v => decide (v.key = k)) with
    | none => simp only [hf] at h; subst h; exact ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
    | some w =>
      simp only [hf] at h; subst h
      have hk : w.key = k := by simpa using List.find?_some hf
      exact ⟨hk, rfl, Or.inl ⟨w, List.mem_of_find?_eq_some hf, hk, rfl, rfl⟩⟩
  · exact Or.inl h

theorem mem_applyChange_del {r : w64} {k : GoString} {s : List EtcdKv} {v : EtcdKv}
    (h : v ∈ applyChange r s (.del k)) : v ∈ s ∧ v.key ≠ k := by
  rw [applyChange_del, List.mem_filter] at h
  exact ⟨h.1, by simpa using h.2⟩

/-- A member whose mod revision is not `r` was there before revision `r`'s changes. -/
theorem mem_applyChanges_modRev {r : w64} :
    ∀ (cs : List Change) (s : List EtcdKv) (v : EtcdKv),
      v ∈ applyChanges r s cs → v.modRev ≠ r → v ∈ s
  | [], _, _, h, _ => h
  | c :: cs, s, v, h, hm => by
    rw [applyChanges_cons] at h
    have h1 := mem_applyChanges_modRev cs _ v h hm
    cases c with
    | put k val l =>
      rcases mem_putKv h1 with h1 | ⟨_, h2, _⟩
      · exact h1
      · exact absurd h2 hm
    | del k => exact (mem_applyChange_del h1).1

/-- A member whose create revision is not `r` had a record of its key with that create
revision before revision `r`'s changes. -/
theorem mem_applyChanges_createRev {r : w64} :
    ∀ (cs : List Change) (s : List EtcdKv) (v : EtcdKv),
      v ∈ applyChanges r s cs → v.createRev ≠ r →
        ∃ w ∈ s, w.key = v.key ∧ w.createRev = v.createRev
  | [], _, v, h, _ => ⟨v, h, rfl, rfl⟩
  | c :: cs, s, v, h, hc => by
    rw [applyChanges_cons] at h
    obtain ⟨w1, hw1, hk1, hc1⟩ := mem_applyChanges_createRev cs _ v h hc
    cases c with
    | put k val l =>
      rcases mem_putKv hw1 with h1 | ⟨hk, _, ⟨w, hw, hwk, hwc, _⟩ | ⟨hcr, _⟩⟩
      · exact ⟨w1, h1, hk1, hc1⟩
      · exact ⟨w, hw, by rw [hwk, ← hk, hk1], by rw [← hwc, hc1]⟩
      · exact absurd (hc1 ▸ hcr) hc
    | del k => exact ⟨w1, (mem_applyChange_del hw1).1, hk1, hc1⟩

/-! ## The revisions of the state's records -/

/-- The revisions of a record of the state at `r`: created at or before its mod revision, which
is at or before `r`. -/
def RevInv (r : Nat) (v : EtcdKv) : Prop :=
  uint.nat v.createRev ≤ uint.nat v.modRev ∧ uint.nat v.modRev ≤ r

theorem revInv_applyChanges (r : Nat) (hr : r < 2 ^ 63) :
    ∀ (cs : List Change) (s : List EtcdKv), (∀ w ∈ s, RevInv r w) →
      ∀ v ∈ applyChanges (W64 (r : Int)) s cs, RevInv r v
  | [], _, hs, v, h => hs v h
  | c :: cs, s, hs, v, h => by
    rw [applyChanges_cons] at h
    refine revInv_applyChanges r hr cs _ ?_ v h
    intro w hw
    cases c with
    | put k val l =>
      rcases mem_putKv hw with h1 | ⟨_, hm, ⟨w0, hw0, _, hwc, _⟩ | ⟨hcr, _⟩⟩
      · exact hs w h1
      · have := hs w0 hw0
        unfold RevInv at *
        rw [hm, hwc, hl_nat_W64 r hr]; omega
      · unfold RevInv; rw [hm, hcr, hl_nat_W64 r hr]; omega
    | del k => exact hs w (mem_applyChange_del hw).1

/-- **The revisions of the state at `r`** (no hypothesis but the word bound): every record's
create revision is at or before its mod revision, which is at or before `r`. -/
theorem stateAt_revInv (log : Log) (hlen : log.length < 2 ^ 63) :
    ∀ r, r < log.length → ∀ v ∈ stateAt log r, RevInv r v
  | 0, hr, v, hv => by
    rw [stateAt_zero log hr] at hv
    exact revInv_applyChanges 0 (by omega) _ [] (by simp) v hv
  | j + 1, hr, v, hv => by
    rw [stateAt_succ log j hr] at hv
    refine revInv_applyChanges (j + 1) (by omega) _ _ ?_ v hv
    intro w hw
    have := stateAt_revInv log hlen j (by omega) w hw
    unfold RevInv at *; omega

/-! ## The versions -/

/-- **Each revision writes a key at most once**: the keys of each revision's changes are
distinct. etcd's check of a transaction's requests (`checkIntervals`: "duplicate key given in
txn request") gives it (`keys_nodup_iff_check`). -/
def NoDupKeysPerRev (log : Log) : Prop := ∀ cs ∈ log, (cs.map Change.key).Nodup

/-- A record of the state at `r`, with positive revisions and version: a record created at
`c` and last modified at `m` has been put at most once in each of the revisions `c, ..., m`. -/
def KvInv (r : Nat) (v : EtcdKv) : Prop :=
  1 ≤ uint.nat v.createRev ∧ uint.nat v.createRev ≤ uint.nat v.modRev ∧ uint.nat v.modRev ≤ r ∧
    1 ≤ uint.nat v.version ∧ uint.nat v.version + uint.nat v.createRev ≤ uint.nat v.modRev + 1

/-- One revision's changes, with distinct keys, keep `KvInv`: a key not yet written in the
revision has a mod revision below it. -/
theorem kvInv_applyChanges (r : Nat) (hr1 : 1 ≤ r) (hr : r < 2 ^ 63) :
    ∀ (cs : List Change) (s : List EtcdKv), (cs.map Change.key).Nodup →
      (∀ w ∈ s, KvInv r w ∧ (w.key ∈ cs.map Change.key → uint.nat w.modRev < r)) →
      ∀ v ∈ applyChanges (W64 (r : Int)) s cs, KvInv r v
  | [], _, _, hs, v, h => (hs v h).1
  | c :: cs, s, hnd, hs, v, h => by
    rw [applyChanges_cons] at h
    rw [List.map_cons, List.nodup_cons] at hnd
    refine kvInv_applyChanges r hr1 hr cs _ hnd.2 ?_ v h
    intro w hw
    cases c with
    | put k val l =>
      rcases mem_putKv hw with h1 | ⟨hk, hm, ⟨w0, hw0, hw0k, hwc, hwv⟩ | ⟨hcr, hver⟩⟩
      · exact ⟨(hs w h1).1, fun hin => (hs w h1).2 (List.mem_cons_of_mem _ hin)⟩
      · obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ := hs w0 hw0
        have hlt := h6 (by rw [hw0k]; exact List.mem_cons_self)
        have hv := hl_succ w0.version (by omega)
        refine ⟨?_, fun hin => absurd (hk ▸ hin) hnd.1⟩
        unfold KvInv; simp only [hm, hwc, hwv, hl_nat_W64 r hr, hv]; omega
      · refine ⟨?_, fun hin => absurd (hk ▸ hin) hnd.1⟩
        have h1 : uint.nat (W64 1) = 1 := by word
        unfold KvInv; simp only [hm, hcr, hver, hl_nat_W64 r hr, h1]; omega
    | del k =>
      have h1 := (mem_applyChange_del hw).1
      exact ⟨(hs w h1).1, fun hin => (hs w h1).2 (List.mem_cons_of_mem _ hin)⟩

theorem stateAt_kvInv (log : Log) (h0 : log[0]? = some []) (hnd : NoDupKeysPerRev log)
    (hlen : log.length < 2 ^ 63) : ∀ r, r < log.length → ∀ v ∈ stateAt log r, KvInv r v
  | 0, _, v, hv => by rw [stateAt_zero_nil log h0] at hv; exact absurd hv List.not_mem_nil
  | j + 1, hr, v, hv => by
    rw [stateAt_succ log j hr] at hv
    refine kvInv_applyChanges (j + 1) (by omega) (by omega) _ _
      (hnd _ (List.getElem_mem hr)) ?_ v hv
    intro w hw
    have := stateAt_kvInv log h0 hnd hlen j (by omega) w hw
    unfold KvInv at *
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, fun _ => ?_⟩ <;> omega

/-! ## The laws -/

/-- **`etcdState_revs` holds of the log**: a record of the state at `r` has a positive create
revision, at or before its mod revision, at or before `r`, and a positive version. Needs
revision 0 empty (in `LogOk`) and `NoDupKeysPerRev` (for the version only). -/
theorem stateAt_revs (log : Log) (hok : LogOk log) (hnd : NoDupKeysPerRev log) (r : Nat)
    (hr : r < log.length) :
    ∀ v ∈ stateAt log r, 0 < sint.Z v.createRev ∧ sint.Z v.createRev ≤ sint.Z v.modRev ∧
      sint.Z v.modRev ≤ r ∧ 0 < sint.Z v.version := by
  intro v hv
  have hlen := hok.len
  obtain ⟨h1, h2, h3, h4, h5⟩ := stateAt_kvInv log hok.wf.1 hnd hlen r hr v hv
  rw [hl_sint_eq _ (by omega), hl_sint_eq v.modRev (by omega), hl_sint_eq v.version (by omega)]
  omega

/-- **`etcdState_modrev_persist` holds of the log**: a record of the state at `a` is in the
state at every revision `b` from its mod revision to `a`. Needs only the word bound. -/
theorem stateAt_modrev_persist (log : Log) (hlen : log.length < 2 ^ 63) (b : Nat) :
    ∀ a, a < log.length → ∀ v ∈ stateAt log a, sint.Z v.modRev ≤ b → b ≤ a → v ∈ stateAt log b
  | 0, _, v, hv, _, hb => by rw [Nat.le_zero.1 hb]; exact hv
  | j + 1, hr, v, hv, hm, hb => by
    by_cases hbe : b = j + 1
    · rw [hbe]; exact hv
    have hri := stateAt_revInv log hlen (j + 1) hr v hv
    unfold RevInv at hri
    rw [hl_sint_eq _ (by omega)] at hm
    rw [stateAt_succ log j hr] at hv
    have hv' := mem_applyChanges_modRev _ _ v hv (by
      intro e
      have := congrArg uint.nat e
      rw [hl_nat_W64 _ (by omega)] at this; omega)
    have hri' := stateAt_revInv log hlen j (by omega) v hv'
    unfold RevInv at hri'
    exact stateAt_modrev_persist log hlen b j (by omega) v hv'
      (by rw [hl_sint_eq _ (by omega)]; exact hm) (by omega)

/-- **`etcdState_create_persist` holds of the log**: a key of the state at `r` created at `c`
is in the state, with create revision `c`, at every revision from `c` to `r`. Needs only the
word bound. -/
theorem stateAt_create_persist (log : Log) (hlen : log.length < 2 ^ 63) (a : Nat) :
    ∀ r, r < log.length → ∀ v ∈ stateAt log r, sint.Z v.createRev ≤ a → a ≤ r →
      ∃ v' ∈ stateAt log a, v'.key = v.key ∧ v'.createRev = v.createRev
  | 0, _, v, hv, _, ha => by rw [Nat.le_zero.1 ha]; exact ⟨v, hv, rfl, rfl⟩
  | j + 1, hr, v, hv, hc, ha => by
    by_cases hae : a = j + 1
    · rw [hae]; exact ⟨v, hv, rfl, rfl⟩
    have hri := stateAt_revInv log hlen (j + 1) hr v hv
    unfold RevInv at hri
    rw [hl_sint_eq _ (by omega)] at hc
    rw [stateAt_succ log j hr] at hv
    obtain ⟨w, hw, hwk, hwc⟩ := mem_applyChanges_createRev _ _ v hv (by
      intro e
      have := congrArg uint.nat e
      rw [hl_nat_W64 _ (by omega)] at this; omega)
    have hri' := stateAt_revInv log hlen j (by omega) w hw
    unfold RevInv at hri'
    obtain ⟨v', hv', hk', hc'⟩ := stateAt_create_persist log hlen a j (by omega) w hw
      (by rw [hl_sint_eq _ (by omega), hwc]; exact_mod_cast hc) (by omega)
    exact ⟨v', hv', hk'.trans hwk, hc'.trans hwc⟩

/-- Two records of one key in a state sorted by key are the same. -/
theorem eq_of_mem_sorted_key {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) {v v' : EtcdKv}
    (hv : v ∈ s) (hv' : v' ∈ s) (hk : v.key = v'.key) : v = v' := by
  have h1 := findKey_of_mem_sorted hs hv
  have h2 := findKey_of_mem_sorted hs hv'
  rw [hk, h2] at h1
  exact (Option.some.inj h1).symm

/-- **`etcdState_modrev_det` holds of the log**: two records of a key, in the states at any two
revisions, with the same mod revision, are the same. Needs only the word bound; in particular
not `NoDupKeysPerRev` (both records are in the state at their mod revision,
`stateAt_modrev_persist`, which has one record per key). -/
theorem stateAt_modrev_det (log : Log) (hlen : log.length < 2 ^ 63) (a b : Nat)
    (ha : a < log.length) (hb : b < log.length) :
    ∀ v ∈ stateAt log a, ∀ v' ∈ stateAt log b, v.key = v'.key → v.modRev = v'.modRev → v = v' := by
  intro v hv v' hv' hk hm
  have hri := stateAt_revInv log hlen a ha v hv
  have hri' := stateAt_revInv log hlen b hb v' hv'
  unfold RevInv at hri hri'
  have hz : sint.Z v.modRev = (uint.nat v.modRev : Int) := hl_sint_eq _ (by omega)
  have h1 := stateAt_modrev_persist log hlen (uint.nat v.modRev) a ha v hv (by rw [hz]; omega)
    hri.2
  have h2 := stateAt_modrev_persist log hlen (uint.nat v.modRev) b hb v' hv'
    (by rw [← hm, hz]; omega) (by rw [hm]; exact hri'.2)
  exact eq_of_mem_sorted_key (stateAt_sorted log _) h1 h2 hk

/-! ## Per prefix: `etcdState r pfx` -/

/-- The state at `r` restricted to the keys with prefix `pfx`: the log's `etcdState r pfx`. -/
def stateAtPfx (log : Log) (r : Nat) (pfx : GoString) : List EtcdKv :=
  (stateAt log r).filter (fun v => decide (pfx <+: v.key))

theorem mem_stateAtPfx {log : Log} {r : Nat} {pfx : GoString} {v : EtcdKv} :
    v ∈ stateAtPfx log r pfx ↔ v ∈ stateAt log r ∧ pfx <+: v.key := by
  unfold stateAtPfx; rw [List.mem_filter, decide_eq_true_iff]

/-- **`etcdState_agree` holds of the log**: one state per revision and prefix (`stateAtPfx` is
a function). -/
theorem stateAtPfx_agree (log : Log) (r : Nat) (pfx : GoString) (s s' : List EtcdKv)
    (h : s = stateAtPfx log r pfx) (h' : s' = stateAtPfx log r pfx) : s = s' := h.trans h'.symm

/-- The log's states per prefix are what the client's `EtcdStateWf` says: keys strictly
increasing, under the prefix. -/
theorem stateAtPfx_wf (log : Log) (r : Nat) (pfx : GoString) :
    EtcdStateWf pfx (stateAtPfx log r pfx) := by
  refine ⟨?_, fun v hv => (mem_stateAtPfx.1 hv).2⟩
  rw [List.pairwise_map]
  exact (stateAt_sorted log r).filter _

theorem stateAtPfx_revs (log : Log) (hok : LogOk log) (hnd : NoDupKeysPerRev log) (r : Nat)
    (hr : r < log.length) (pfx : GoString) :
    ∀ v ∈ stateAtPfx log r pfx, 0 < sint.Z v.createRev ∧ sint.Z v.createRev ≤ sint.Z v.modRev ∧
      sint.Z v.modRev ≤ r ∧ 0 < sint.Z v.version :=
  fun v hv => stateAt_revs log hok hnd r hr v (mem_stateAtPfx.1 hv).1

theorem stateAtPfx_create_persist (log : Log) (hlen : log.length < 2 ^ 63) (r a : Nat)
    (hr : r < log.length) (pfx : GoString) :
    ∀ v ∈ stateAtPfx log r pfx, sint.Z v.createRev ≤ a → a ≤ r →
      ∃ v' ∈ stateAtPfx log a pfx, v'.key = v.key ∧ v'.createRev = v.createRev := by
  intro v hv hc ha
  have hv := mem_stateAtPfx.1 hv
  obtain ⟨v', hv', hk, hc'⟩ := stateAt_create_persist log hlen a r hr v hv.1 hc ha
  exact ⟨v', mem_stateAtPfx.2 ⟨hv', hk ▸ hv.2⟩, hk, hc'⟩

theorem stateAtPfx_modrev_det (log : Log) (hlen : log.length < 2 ^ 63) (a b : Nat)
    (ha : a < log.length) (hb : b < log.length) (pfx : GoString) :
    ∀ v ∈ stateAtPfx log a pfx, ∀ v' ∈ stateAtPfx log b pfx, v.key = v'.key →
      v.modRev = v'.modRev → v = v' :=
  fun v hv v' hv' => stateAt_modrev_det log hlen a b ha hb v (mem_stateAtPfx.1 hv).1 v'
    (mem_stateAtPfx.1 hv').1

theorem stateAtPfx_modrev_persist (log : Log) (hlen : log.length < 2 ^ 63) (a b : Nat)
    (ha : a < log.length) (pfx : GoString) :
    ∀ v ∈ stateAtPfx log a pfx, sint.Z v.modRev ≤ b → b ≤ a → v ∈ stateAtPfx log b pfx := by
  intro v hv hm hb
  have hv := mem_stateAtPfx.1 hv
  exact mem_stateAtPfx.2 ⟨stateAt_modrev_persist log hlen b a ha v hv.1 hm hb, hv.2⟩

/-! ## Reached revisions keep their state -/

/-- **A revision's state is fixed once reached**: a longer log (the history later) has the same
state at every revision of the shorter one. The log analogue of `etcdReachedAt`'s use: what was
learned of a reached revision stays true. -/
theorem stateAt_of_prefix {log log' : Log} (h : log <+: log') {r : Nat} (hr : r < log.length) :
    stateAt log' r = stateAt log r := by
  obtain ⟨t, rfl⟩ := h
  unfold stateAt
  rw [List.take_append_of_le_length (by omega)]

theorem stateAtPfx_of_prefix {log log' : Log} (h : log <+: log') {r : Nat} (hr : r < log.length)
    (pfx : GoString) : stateAtPfx log' r pfx = stateAtPfx log r pfx := by
  unfold stateAtPfx; rw [stateAt_of_prefix h hr]

/-! ## A commit keeps the hypotheses -/

/-- The deletes of a revision's changes `cs` (at revision `r`, on the state `s` before it) are
of keys present when they run: `LogWf`'s condition on one revision. -/
def DelsPresent (r : w64) (s : List EtcdKv) (cs : List Change) : Prop :=
  ∀ (i : Nat) (k : GoString), cs[i]? = some (.del k) →
    (findKey k (applyChanges r s (cs.take i))).isSome

/-- The keys a revision puts. -/
def putKeysOf (cs : List Change) : List GoString :=
  cs.filterMap fun c => match c with | .put k _ _ => some k | .del _ => none

/-- The keys a revision deletes. -/
def delKeysOf (cs : List Change) : List GoString :=
  cs.filterMap fun c => match c with | .put .. => none | .del k => some k

/-- **`LogOk` is kept by a commit** whose deletes are of present keys. -/
theorem LogOk.snoc {log : Log} (hok : LogOk log) {pend : List Change}
    (hdel : DelsPresent (W64 (log.length : Int)) (stateAfter log) pend)
    (hlen : log.length + 1 < 2 ^ 63) (hpl : pend.length < 2 ^ 63) : LogOk (log ++ [pend]) := by
  have hpos : 0 < log.length := (List.getElem?_eq_some_iff.1 hok.wf.1).1
  refine ⟨⟨?_, fun r cs i k hr hi => ?_⟩, by simp; omega, fun cs hcs => ?_⟩
  · rw [List.getElem?_append_left hpos]; exact hok.wf.1
  · by_cases hlt : r < log.length
    · rw [List.getElem?_append_left hlt] at hr
      rw [stateAt_append_lt _ _ (by omega)]
      exact hok.wf.2 r cs i k hr hi
    · rw [List.getElem?_append_right (by omega)] at hr
      have hr0 : r - log.length = 0 := by
        have := (List.getElem?_eq_some_iff.1 hr).1
        simp at this; omega
      rw [hr0] at hr
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      have hreq : r = log.length := by omega
      subst hreq
      rw [stateAt_append_lt _ _ (by omega), stateAt_last]
      exact hdel i k hi
  · rcases List.mem_append.1 hcs with h | h
    · exact hok.cs cs h
    · rw [List.mem_singleton.1 h]; exact hpl

/-- **`NoDupKeysPerRev` is kept by a commit** iff the commit's keys are distinct. -/
theorem NoDupKeysPerRev.snoc_iff (log : Log) (pend : List Change) :
    NoDupKeysPerRev (log ++ [pend]) ↔ NoDupKeysPerRev log ∧ (pend.map Change.key).Nodup := by
  unfold NoDupKeysPerRev
  constructor
  · intro h
    exact ⟨fun cs hcs => h cs (List.mem_append_left _ hcs),
      h pend (List.mem_append_right _ (List.mem_singleton_self _))⟩
  · rintro ⟨h1, h2⟩ cs hcs
    rcases List.mem_append.1 hcs with h | h
    · exact h1 cs h
    · rw [List.mem_singleton.1 h]; exact h2

theorem findKey_isSome_iff (k : GoString) (s : List EtcdKv) :
    (findKey k s).isSome ↔ ∃ v ∈ s, v.key = k := by
  unfold findKey
  rw [List.find?_isSome]
  simp

/-- A key absent from a state stays absent through changes that do not put it. -/
theorem absent_applyChanges {r : w64} {k : GoString} :
    ∀ (cs : List Change) (s : List EtcdKv), (∀ v ∈ s, v.key ≠ k) → k ∉ putKeysOf cs →
      ∀ v ∈ applyChanges r s cs, v.key ≠ k
  | [], _, hs, _ => hs
  | c :: cs, s, hs, hp => by
    rw [applyChanges_cons]
    cases c with
    | put k' val l =>
      have hk' : k' ≠ k := fun e => hp (by simp [putKeysOf, e])
      have hp' : k ∉ putKeysOf cs := fun h => hp (by simp only [putKeysOf, List.filterMap_cons]; exact List.mem_cons_of_mem _ h)
      refine absent_applyChanges cs _ ?_ hp'
      intro v hv
      rcases mem_putKv hv with h | ⟨h, _⟩
      · exact hs v h
      · rw [h]; exact hk'
    | del k' =>
      have hp' : k ∉ putKeysOf cs := by simpa [putKeysOf] using hp
      exact absent_applyChanges cs _ (fun v hv => hs v (mem_applyChange_del hv).1) hp'

/-- **The exact condition for a revision's keys to be distinct**: for a revision whose deletes
are of present keys (`DelsPresent`), its keys are distinct iff the keys it puts are distinct and
none of them is also deleted, which is etcd's check of a transaction's requests
(`checkIntervals`: distinct put keys, no put key in a delete's range). Two deletes of one key need
a put of it between them (the first removes it). -/
theorem keys_nodup_iff_check {r : w64} :
    ∀ (cs : List Change) (s : List EtcdKv), DelsPresent r s cs →
      ((cs.map Change.key).Nodup ↔
        (putKeysOf cs).Nodup ∧ ∀ k ∈ putKeysOf cs, k ∉ delKeysOf cs)
  | [], _, _ => by simp [putKeysOf]
  | c :: cs, s, hd => by
    have hd' : DelsPresent r (applyChange r s c) cs := by
      intro i k hi
      have := hd (i + 1) k (by simpa using hi)
      rwa [List.take_succ_cons, applyChanges_cons] at this
    have ih := keys_nodup_iff_check cs _ hd'
    have hsub_p : ∀ k ∈ putKeysOf cs, k ∈ cs.map Change.key := by
      intro k hk
      obtain ⟨c', hc', hck⟩ := List.mem_filterMap.1 hk
      refine List.mem_map.2 ⟨c', hc', ?_⟩
      cases c' <;> simp_all [Change.key]
    have hsub_d : ∀ k ∈ delKeysOf cs, k ∈ cs.map Change.key := by
      intro k hk
      obtain ⟨c', hc', hck⟩ := List.mem_filterMap.1 hk
      refine List.mem_map.2 ⟨c', hc', ?_⟩
      cases c' <;> simp_all [Change.key]
    rw [List.map_cons, List.nodup_cons, ih]
    cases c with
    | put k val l =>
      simp only [putKeysOf, delKeysOf, List.filterMap_cons, List.nodup_cons, List.mem_cons,
        forall_eq_or_imp, Change.key] at *
      constructor
      · rintro ⟨hk, hn, hdis⟩
        exact ⟨⟨fun h => hk (hsub_p k h), hn⟩, fun h => hk (hsub_d k h), hdis⟩
      · rintro ⟨⟨hk, hn⟩, hkd, hdis⟩
        refine ⟨fun hin => ?_, hn, hdis⟩
        obtain ⟨c', hc', hck⟩ := List.mem_map.1 hin
        cases c' with
        | put k' _ _ => exact hk (List.mem_filterMap.2 ⟨_, hc', by simp [Change.key] at hck; simp [hck]⟩)
        | del k' => exact hkd (List.mem_filterMap.2 ⟨_, hc', by simp [Change.key] at hck; simp [hck]⟩)
    | del k =>
      have hpk : putKeysOf (Change.del k :: cs) = putKeysOf cs := by simp [putKeysOf]
      have hdk : delKeysOf (Change.del k :: cs) = k :: delKeysOf cs := by simp [delKeysOf]
      rw [hpk, hdk]
      simp only [Change.key, List.mem_cons]
      constructor
      · rintro ⟨hknot, hn, hdis⟩
        exact ⟨hn, fun k' hk' h => h.elim (fun e => hknot (e ▸ hsub_p k' hk')) (hdis k' hk')⟩
      · rintro ⟨hn, hdis⟩
        refine ⟨fun hin => ?_, hn, fun k' hk' h => hdis k' hk' (Or.inr h)⟩
        -- `k` is deleted again later, at some `i`: it must be present then, but it was deleted
        -- by `c` and no change of `cs` puts it
        have hkp : k ∉ putKeysOf cs := fun h => hdis k h (Or.inl rfl)
        obtain ⟨c', hc', hck⟩ := List.mem_map.1 hin
        obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc'
        cases c' with
        | put k' _ _ =>
          exact hkp (List.mem_filterMap.2 ⟨_, hc', by simp [Change.key] at hck; simp [hck]⟩)
        | del k' =>
          simp only [Change.key] at hck
          subst hck
          have hpres := hd' i k' (by rw [List.getElem?_eq_getElem hi, hci])
          rw [findKey_isSome_iff] at hpres
          obtain ⟨v, hv, hvk⟩ := hpres
          refine absent_applyChanges (cs.take i) _ (fun w hw => (mem_applyChange_del hw).2)
            (fun h => hkp ?_) v hv hvk
          obtain ⟨c'', hc'', e⟩ := List.mem_filterMap.1 h
          exact List.mem_filterMap.2 ⟨c'', List.mem_of_mem_take hc'', e⟩

/-- **`NoDupKeysPerRev` is kept by a commit** that passes etcd's check: its deletes are of
present keys, its put keys are distinct and none is deleted. -/
theorem NoDupKeysPerRev.snoc {log : Log} (hnd : NoDupKeysPerRev log) {pend : List Change}
    (hdel : DelsPresent (W64 (log.length : Int)) (stateAfter log) pend)
    (hput : (putKeysOf pend).Nodup) (hdis : ∀ k ∈ putKeysOf pend, k ∉ delKeysOf pend) :
    NoDupKeysPerRev (log ++ [pend]) :=
  (NoDupKeysPerRev.snoc_iff log pend).2 ⟨hnd, (keys_nodup_iff_check pend _ hdel).2 ⟨hput, hdis⟩⟩

/-- A range delete's keys (`(srvSel s …).map EtcdKv.key`, `delKeys_eq`), of a sorted state,
are distinct. -/
theorem sel_keys_nodup {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (p : EtcdKv → Bool) :
    ((s.filter p).map EtcdKv.key).Nodup := by
  have h : ((s.filter p).map EtcdKv.key).Pairwise go.GoStringLt := by
    rw [List.pairwise_map]; exact hs.filter _
  refine h.imp ?_
  intro a b hab e
  rw [e] at hab
  exact goStringLt_irrefl _ hab

end txn
end EtcdGrove
end Perennial
