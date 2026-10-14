/-
The leasing protocol as a premise on etcd's history (Lean-first, no Rocq counterpart). See
`decisions.md`, "Leasing: the protocol as a premise on the history".

`client/v3/leasing` caches a key `k` at a client (the *holder*) while the holder's *lease key*
`pfx ++ k` exists: a reader acquires it (a transaction putting `pfx ++ k` with its session's lease
if it does not exist), and every leasing client modifies `k` in a transaction guarded by
`CreateRevision(pfx ++ k) < g + 1`, where `g` is `0` unless the writer is the holder (then `g` is
its entry's revision, at least the lease key's create revision): a writer that is not the holder
first puts `"REVOKE"` into the lease key (`WithIgnoreLease`, keeping the holder's lease), waits
until the holder has evicted its entry and deleted the lease key, and retries. Whether etcd's
history obeys this is a fact about the deployment (every writer of a data key uses a leasing
client with the same prefix; nobody else writes lease keys), not about the code of one client, so
it is a premise, `LeasingProtocol pfx h`, which the leasing theorems take (a hypothesis, not an
axiom).

**The history** (`LeasingHist`): etcd's whole-keyspace state at each revision `z ≥ 0`
(`h.st z`, linked to the model by `etcdState r "" (h.st r)`), and for each revision the lease of
the leasing session whose transaction made it (`h.writer z`; anything for another writer). The
model's `etcdState` gives states only at revisions a client observes; the premise speaks of every
revision, so that a property can be carried from one observed revision to another.

**The premise** (`LeasingStepOk`), for every revision `z > 0` and data key `k` (a key outside the
lease prefix, `LeasingDataKey`):
1. if `k`'s record changes from `z - 1` to `z`, then either `pfx ++ k` is absent at `z - 1`, or it
   is present with a lease `L ≠ 0` and the transaction at `z` is the holder's (`h.writer z = L`):
   **only the holder writes a leased key**;
2. a lease key present at `z - 1` and at `z` with the same create revision keeps its lease (the
   only write to an existing lease key is the `"REVOKE"` put, `WithIgnoreLease`);
3. etcd's states have unique keys (`EtcdStateWf ""`, true of etcd).

**The key lemma** (`leased_value_stable`): if `pfx ++ k` is present at `a` with create revision `c`
and lease `L`, and present with create revision `c` at `b ≥ a`, and the holder `L` committed no
transaction in `(a, b]`, then `k`'s record at `b` is its record at `a`. **A revoked lease still
protects** (`revoked_protects`): after `"REVOKE"` is put into the incarnation `c` of the lease key
at `a`, a transaction of anyone but the holder changes `k` at `z > a` only if that incarnation is
gone at `z - 1`.

**The lease-expiry window** is not excluded by the premise but by its statement: when the
holder's session lease expires, etcd deletes the lease key (a step that changes no data key), and
writers may then change `k`, while the holder's cache still holds `k` until it notices; the
lemmas say what holds *while the lease key exists*, which the holder cannot observe locally (a
cache answer is `k`'s record at a revision at which the lease key existed, not a linearizable
one). See `decisions.md`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## The protocol -/

/-- The record of the key `k` in the state `s` (`none`: absent). -/
def kvOf (s : List EtcdKv) (k : GoString) : Option EtcdKv := s.find? (fun v => decide (v.key = k))

/-- A data key of a leasing KV with lease prefix `pfx`: outside the prefix. A key under `pfx` is a
lease key (`pfx ++ k`) or not used: the leasing KV caches nothing under its own prefix. -/
def LeasingDataKey (pfx k : GoString) : Prop := ¬ pfx <+: k

/-- etcd's history, as the protocol sees it: the whole-keyspace state at each revision `z ≥ 0`,
and the session lease of the leasing client whose transaction made revision `z` (anything for a
revision not made by a leasing client). -/
structure LeasingHist where
  st : Int → List EtcdKv
  writer : Int → w64

/-- **The protocol at revision `z`** (`z > 0`; see the module docstring): (1) a data key `k`
changes only while `pfx ++ k` is absent, or by its holder (the lease key's lease, never `0`);
(2) a lease key that stays with the same create revision keeps its lease; (3) keys are unique. -/
def LeasingStepOk (pfx : GoString) (h : LeasingHist) (z : Int) : Prop :=
  (∀ k, LeasingDataKey pfx k → kvOf (h.st (z - 1)) k ≠ kvOf (h.st z) k →
    ∀ lv, kvOf (h.st (z - 1)) (pfx ++ k) = some lv → lv.lease ≠ W64 0 ∧ h.writer z = lv.lease) ∧
  (∀ k lv lv', LeasingDataKey pfx k → kvOf (h.st (z - 1)) (pfx ++ k) = some lv →
    kvOf (h.st z) (pfx ++ k) = some lv' → lv'.createRev = lv.createRev → lv'.lease = lv.lease)

section premise
variable {GF : BundledGFunctors}
variable [EM : EtcdModel GF]

/-- **The leasing protocol premise**: `h` is etcd's history (its state at every revision
`r ≥ 0` is `h.st r`, with unique keys) and every revision `0 < z < 2^63` obeys the protocol
(`LeasingStepOk`). Persistent. A hypothesis the leasing theorems take: a fact about the
deployment (all writers of data keys are leasing clients of prefix `pfx`), not an axiom. -/
def LeasingProtocol (pfx : GoString) (h : LeasingHist) : IProp GF :=
  iprop(□ (∀ r : w64, ⌜0 ≤ sint.Z r⌝ -∗ etcdState r ([] : GoString) (h.st (sint.Z r))) ∗
    ⌜∀ z : Int, 0 ≤ z → z < 2 ^ 63 → EtcdStateWf [] (h.st z)⌝ ∗
    ⌜∀ z : Int, 0 < z → z < 2 ^ 63 → LeasingStepOk pfx h z⌝)

instance LeasingProtocol_persistent (pfx : GoString) (h : LeasingHist) :
    Persistent (LeasingProtocol (GF := GF) pfx h) := by
  unfold LeasingProtocol; infer_instance

end premise

/-! ## Pure facts about a history -/

/-- The history laws `h` inherits from the model (`etcdState_revs`, `etcdState_create_persist`)
and the premise (unique keys, the protocol), over revisions `0 ≤ z < 2^63`. -/
structure LeasingHistOk (pfx : GoString) (h : LeasingHist) : Prop where
  wf : ∀ z : Int, 0 ≤ z → z < 2 ^ 63 → EtcdStateWf [] (h.st z)
  revs : ∀ z : Int, 0 ≤ z → z < 2 ^ 63 → ∀ v ∈ h.st z,
    0 < sint.Z v.createRev ∧ sint.Z v.createRev ≤ sint.Z v.modRev ∧ sint.Z v.modRev ≤ z
  persist : ∀ z1 z2 : Int, 0 ≤ z1 → z1 ≤ z2 → z2 < 2 ^ 63 → ∀ v ∈ h.st z2,
    sint.Z v.createRev ≤ z1 → ∃ v' ∈ h.st z1, v'.key = v.key ∧ v'.createRev = v.createRev
  step : ∀ z : Int, 0 < z → z < 2 ^ 63 → LeasingStepOk pfx h z

/-- In a state with unique keys, a member is the record of its key. -/
theorem kvOf_of_mem (s : List EtcdKv) (v : EtcdKv) (hwf : EtcdStateWf [] s) (hv : v ∈ s) :
    kvOf s v.key = some v := by
  unfold kvOf
  obtain ⟨hpw, -⟩ := hwf
  induction s with
  | nil => simp at hv
  | cons x xs ih =>
    rw [List.map_cons, List.pairwise_cons] at hpw
    rcases List.mem_cons.1 hv with rfl | hv'
    · simp
    · have hne : x.key ≠ v.key := by
        intro he
        have := hpw.1 v.key (List.mem_map_of_mem hv')
        rw [he] at this
        exact goStringLt_irrefl _ this
      simp only [List.find?_cons, hne, decide_false]
      exact ih hv' hpw.2

/-- The record of a key is a member of the state, with that key. -/
theorem kvOf_mem {s : List EtcdKv} {k : GoString} {v : EtcdKv} (h : kvOf s k = some v) :
    v ∈ s ∧ v.key = k := by
  unfold kvOf at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- **Along a lease incarnation** (pure): if the lease key `pfx ++ k` has, at `a`, the record `lv`
(create revision `c`, lease `L`), and at `b ≥ a` a record with create revision `c`, then at every
`z ∈ [a, b]` it has a record with create revision `c` and lease `L`, and if the holder `L`
committed no transaction in `(a, z]`, `k`'s record at `z` is its record at `a`. -/
theorem leased_incarnation (pfx k : GoString) (h : LeasingHist) (hok : LeasingHistOk pfx h)
    (hk : LeasingDataKey pfx k) (a b : Int) (lv lb : EtcdKv) (ha : 0 ≤ a) (hb : b < 2 ^ 63)
    (hlv : kvOf (h.st a) (pfx ++ k) = some lv) (hlb : kvOf (h.st b) (pfx ++ k) = some lb)
    (hc : lb.createRev = lv.createRev) :
    ∀ z : Int, a ≤ z → z ≤ b →
      (∃ lz, kvOf (h.st z) (pfx ++ k) = some lz ∧ lz.createRev = lv.createRev ∧
        lz.lease = lv.lease) ∧
      ((∀ y, a < y → y ≤ z → h.writer y ≠ lv.lease) → kvOf (h.st z) k = kvOf (h.st a) k) := by
  have key : ∀ n : Nat, a + n ≤ b →
      (∃ lz, kvOf (h.st (a + n)) (pfx ++ k) = some lz ∧ lz.createRev = lv.createRev ∧
        lz.lease = lv.lease) ∧
      ((∀ y, a < y → y ≤ a + n → h.writer y ≠ lv.lease) →
        kvOf (h.st (a + n)) k = kvOf (h.st a) k) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [show a + ((0 : Nat) : Int) = a by omega]
      exact ⟨⟨lv, hlv, rfl, rfl⟩, fun _ => rfl⟩
    | succ n ih =>
      intro hzb
      have hcast : a + ((n + 1 : Nat) : Int) = a + n + 1 := by push_cast; omega
      rw [hcast] at hzb ⊢
      obtain ⟨⟨lz, hlz, hlzc, hlzl⟩, hdata⟩ := ih (by omega)
      -- the lease key is present at `a + n + 1` with create revision `c` (from `b`)
      obtain ⟨hlbm, hlbk⟩ := kvOf_mem hlb
      obtain ⟨hlvm, -⟩ := kvOf_mem hlv
      have hca : sint.Z lv.createRev ≤ a := by
        have := hok.revs a ha (by omega) lv hlvm; omega
      obtain ⟨v', hv'm, hv'k, hv'c⟩ := hok.persist (a + n + 1) b (by omega) hzb hb lb hlbm
        (by rw [hc]; omega)
      have hv'kv : kvOf (h.st (a + n + 1)) (pfx ++ k) = some v' := by
        rw [← hlbk, ← hv'k]; exact kvOf_of_mem _ _ (hok.wf (a + n + 1) (by omega) (by omega)) hv'm
      have hstep := hok.step (a + n + 1) (by omega) (by omega)
      unfold LeasingStepOk at hstep
      rw [show a + n + 1 - 1 = a + n by omega] at hstep
      have hlease : v'.lease = lz.lease :=
        hstep.2 k lz v' hk hlz hv'kv (by rw [hv'c, hc, hlzc])
      refine ⟨⟨v', hv'kv, by rw [hv'c, hc], by rw [hlease, hlzl]⟩, ?_⟩
      intro hw
      rw [← hdata (fun y hy1 hy2 => hw y hy1 (by omega))]
      apply Classical.byContradiction
      intro hne
      have := (hstep.1 k hk (Ne.symm hne) lz hlz).2
      exact hw (a + n + 1) (by omega) (Int.le_refl _) (by rw [this, hlzl])
  intro z hz1 hz2
  have hz : z = a + ((z - a).toNat : Int) := by omega
  rw [hz]
  exact key (z - a).toNat (by omega)

theorem leasing_pure_forall_intro {PROP : Type _} [BI PROP] {P : PROP} {α : Sort _}
    {φ : α → Prop} (h : ∀ x, P ⊢ ⌜φ x⌝) : P ⊢ ⌜∀ x, φ x⌝ :=
  (forall_intro h).trans pure_forall.2

section lemmas
variable {GF : BundledGFunctors}
variable [EM : EtcdModel GF]

/-- The premise gives etcd's state at every revision `r ≥ 0`: `h.st r`. -/
theorem leasingProtocol_state (pfx : GoString) (h : LeasingHist) (r : w64) (hr : 0 ≤ sint.Z r) :
    LeasingProtocol (GF := GF) pfx h ⊢ etcdState r [] (h.st (sint.Z r)) := by
  unfold LeasingProtocol
  iintro ⟨#Hst, -, -⟩
  iapply Hst $$ %r %hr

/-- A state of etcd at `r ≥ 0` (whole keyspace) is the history's. -/
theorem leasingProtocol_agree (pfx : GoString) (h : LeasingHist) (r : w64) (s : List EtcdKv)
    (hr : 0 ≤ sint.Z r) :
    LeasingProtocol (GF := GF) pfx h ∗ etcdState r [] s ⊢ ⌜s = h.st (sint.Z r)⌝ := by
  iintro ⟨#Hp, Hs⟩
  ihave Hh := leasingProtocol_state pfx h r hr $$ Hp
  iapply etcdState_agree r [] s (h.st (sint.Z r)) $$ [$Hs $Hh]

/-- The revision law (`etcdState_revs`) of the history's states. -/
theorem leasingProtocol_revs (pfx : GoString) (h : LeasingHist) :
    LeasingProtocol (GF := GF) pfx h ⊢ ⌜∀ z : Int, 0 ≤ z → z < 2 ^ 63 → ∀ v ∈ h.st z,
      0 < sint.Z v.createRev ∧ sint.Z v.createRev ≤ sint.Z v.modRev ∧
        sint.Z v.modRev ≤ z⌝ := by
  refine leasing_pure_forall_intro fun z => ?_
  by_cases hz : 0 ≤ z ∧ z < 2 ^ 63
  · have hzr : sint.Z (W64 z) = z := by word
    iintro #Hp
    ihave Hs := leasingProtocol_state pfx h (W64 z) (by rw [hzr]; exact hz.1) $$ Hp
    rw [hzr]
    ihave %H := etcdState_revs (W64 z) [] (h.st z) $$ Hs
    ipureintro
    intro _ _ v hv
    have := H v hv
    rw [hzr] at this
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  · iintro _
    ipureintro
    intro h0 h1; exact absurd ⟨h0, h1⟩ hz

/-- The create-revision persistence law (`etcdState_create_persist`) of the history's states. -/
theorem leasingProtocol_persist (pfx : GoString) (h : LeasingHist) :
    LeasingProtocol (GF := GF) pfx h ⊢ ⌜∀ z1 z2 : Int, 0 ≤ z1 → z1 ≤ z2 → z2 < 2 ^ 63 →
      ∀ v ∈ h.st z2, sint.Z v.createRev ≤ z1 →
        ∃ v' ∈ h.st z1, v'.key = v.key ∧ v'.createRev = v.createRev⌝ := by
  refine leasing_pure_forall_intro fun z1 => leasing_pure_forall_intro fun z2 => ?_
  by_cases hz : 0 ≤ z1 ∧ z1 ≤ z2 ∧ z2 < 2 ^ 63
  · have hz1 : sint.Z (W64 z1) = z1 := by word
    have hz2 : sint.Z (W64 z2) = z2 := by word
    iintro #Hp
    ihave Hs1 := leasingProtocol_state pfx h (W64 z1) (by rw [hz1]; exact hz.1) $$ Hp
    ihave Hs2 := leasingProtocol_state pfx h (W64 z2) (by rw [hz2]; omega) $$ Hp
    rw [hz1, hz2]
    ihave %H := etcdState_create_persist (W64 z2) (W64 z1) [] (h.st z2) (h.st z1) $$ [$Hs2 $Hs1]
    ipureintro
    intro _ _ _ v hv hc
    exact H v hv (by rw [hz1]; exact hc) (by rw [hz1, hz2]; exact hz.2.1)
  · iintro _
    ipureintro
    intro h0 h1 h2; exact absurd ⟨h0, h1, h2⟩ hz

/-- The pure laws of the history the premise names (`LeasingHistOk`), from the premise and the
model's history laws. -/
theorem leasingProtocol_ok (pfx : GoString) (h : LeasingHist) :
    LeasingProtocol (GF := GF) pfx h ⊢ ⌜LeasingHistOk pfx h⌝ := by
  iintro #Hp
  ihave %Hrevs := leasingProtocol_revs pfx h $$ Hp
  ihave %Hpersist := leasingProtocol_persist pfx h $$ Hp
  unfold LeasingProtocol
  icases Hp with ⟨-, %Hwf, %Hstep⟩
  ipureintro
  exact ⟨Hwf, Hrevs, Hpersist, Hstep⟩

/-- **The key lemma: a leased value is stable.** If the lease key `pfx ++ k` of the data key `k`
has, at revision `a`, the record `lv` (create revision `c`, lease `L`: its holder's session), and
at `b ≥ a` a record with the same create revision `c` (the same incarnation, still there), and the
holder `L` committed no transaction in `(a, b]`, then `k`'s record at `b` is its record at `a`. (For
the holder's cache: an entry acquired at `a = c` holds `k`'s record at `c`, which is `k`'s record
at every revision until the lease key is deleted, as long as the holder itself does not write
`k`; its own writes are reflected in the cache by `Update`/`Delete`.) -/
theorem leased_value_stable (pfx k : GoString) (h : LeasingHist) (a b : w64)
    (sa sb : List EtcdKv) (lv lb : EtcdKv) (hk : LeasingDataKey pfx k)
    (hab : sint.Z a ≤ sint.Z b) (hlv : kvOf sa (pfx ++ k) = some lv)
    (hlb : kvOf sb (pfx ++ k) = some lb) (hc : lb.createRev = lv.createRev)
    (hw : ∀ z : Int, sint.Z a < z → z ≤ sint.Z b → h.writer z ≠ lv.lease) :
    LeasingProtocol (GF := GF) pfx h ∗ etcdState a [] sa ∗ etcdState b [] sb ⊢
      ⌜kvOf sb k = kvOf sa k⌝ := by
  iintro ⟨#Hp, Ha, Hb⟩
  ihave %Hrevs := etcdState_revs a [] sa $$ Ha
  have ha0 : 0 ≤ sint.Z a := by
    have := Hrevs lv (kvOf_mem hlv).1; omega
  ihave %Hok := leasingProtocol_ok pfx h $$ Hp
  ihave %Hsa := leasingProtocol_agree pfx h a sa ha0 $$ [$Hp $Ha]
  ihave %Hsb := leasingProtocol_agree pfx h b sb (by omega) $$ [$Hp $Hb]
  subst Hsa Hsb
  ipureintro
  have hb : sint.Z b < 2 ^ 63 := by word
  exact (leased_incarnation pfx k h Hok hk (sint.Z a) (sint.Z b) lv lb ha0 hb hlv hlb hc
    (sint.Z b) hab (Int.le_refl _)).2 hw

/-- **A revoked lease still protects.** If the lease key `pfx ++ k` has, at `a`, the record `lv`
(create revision `c`, lease `L`), e.g. after a writer put `"REVOKE"` into it (a put that keeps the
create revision and, `WithIgnoreLease`, the lease), then a transaction at `z > a` of anyone but the
holder (`h.writer z ≠ L`) that changes `k` runs after the incarnation `c` is gone: at `z - 1` the
lease key is absent or has another create revision. So a writer that revoked must wait for the
holder's delete (`waitRescind`) before its write can succeed. -/
theorem revoked_protects (pfx k : GoString) (h : LeasingHist) (a : w64) (sa : List EtcdKv)
    (lv : EtcdKv) (hk : LeasingDataKey pfx k) (hlv : kvOf sa (pfx ++ k) = some lv) (z : Int)
    (haz : sint.Z a < z) (hz : z < 2 ^ 63)
    (hchg : kvOf (h.st (z - 1)) k ≠ kvOf (h.st z) k) (hw : h.writer z ≠ lv.lease) :
    LeasingProtocol (GF := GF) pfx h ∗ etcdState a [] sa ⊢
      ⌜∀ lz, kvOf (h.st (z - 1)) (pfx ++ k) = some lz → lz.createRev ≠ lv.createRev⌝ := by
  iintro ⟨#Hp, Ha⟩
  ihave %Hrevs := etcdState_revs a [] sa $$ Ha
  have ha0 : 0 ≤ sint.Z a := by
    have := Hrevs lv (kvOf_mem hlv).1; omega
  ihave %Hok := leasingProtocol_ok pfx h $$ Hp
  ihave %Hsa := leasingProtocol_agree pfx h a sa ha0 $$ [$Hp $Ha]
  subst Hsa
  ipureintro
  intro lz hlz hc
  obtain ⟨⟨lz', hlz', -, hlease⟩, -⟩ := leased_incarnation pfx k h Hok hk (sint.Z a) (z - 1) lv lz
    ha0 (by omega) hlv hlz hc (z - 1) (by omega) (Int.le_refl _)
  rw [hlz] at hlz'
  cases hlz'
  have := (Hok.step z (by omega) hz).1 k hk hchg lz hlz
  exact hw (by rw [this.2, hlease])

end lemmas

end EtcdGrove
end Perennial
