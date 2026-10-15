/-
`client/v3/concurrency`'s `Election` (`election.go`): the vocabulary of
`Spec/go_etcd_io/etcd/client/v3/concurrency/{NewElection,ResumeElection,Election__*}.lean`, and the
pure facts the exported results use. Lean-first (no Rocq counterpart). See `decisions.md`,
"Election: the mutex's leader fact, no final check, what `Observe` can promise".

**The protocol** (the mutex's): a campaign on the prefix `pfx` (`NewElection`'s argument with a
`/`) puts the key `pfx ++ hex(lease)`, with the proposal as its value, in a transaction that creates
it only if it does not exist (`Campaign`); the key with the smallest create revision under `pfx` is
the leader; a candidate waits until every key created before its own is deleted (`waitDeletes`).
`Proclaim` rewrites the value if the key still has the campaign's create revision, `Resign` deletes
it under the same guard.

**The leader fact** `leaderAt pfx key c R` is the mutex's ownership fact (`lockedAt`): at `R`,
under `pfx`, `key` is present with create revision `c` and no key has a smaller one. Exclusion is
the mutex's (`lockedAt_exclusion`). **`Campaign` does not check its key after the wait**, so its
`nil` gives `leaderAt` **or** `campaignLost` (no key older than `c` is left, but `key` is not there
with create revision `c`: deleted, or deleted and re-created).

**`Observe`'s responses** (`observedAt pfx v R`): the key-value `v` is in etcd's state at `R`, and
either it is the leader there, or (only if the watch skipped events, which etcd's does not but the
client contract does not promise) one of two weaker facts anchored at an earlier revision.

**The election** (`isElection e s γ client id pfx`, persistent: the session `s` and the prefix
`pfx`; the client's contract for `pfx`, `isEtcdMutexClient`) and its **state** (`electionState e s
st`, exclusive: `leaderKey`, `leaderRev`, `leaderSession`, `hdr`; `leaderSession` is nil or `s`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

/-! ## Pure facts -/

/-- In the state `s`, the key-value `v` is the leader: present, and no key has a smaller create
revision. -/
def LeaderKvState (v : EtcdKv) (s : List EtcdKv) : Prop :=
  v ∈ s ∧ ∀ w ∈ s, sint.Z v.createRev ≤ sint.Z w.createRev

theorem LeaderKvState.locked {v : EtcdKv} {s : List EtcdKv} (h : LeaderKvState v s) :
    LockedState v.key v.createRev s :=
  ⟨⟨v, h.1, rfl, rfl⟩, h.2⟩

/-- A campaign for `key` (created at `c`) that lost its key: no key with a create revision below
`c` is left, but `key` is not present with create revision `c` (deleted, or re-created). -/
def LostState (key : GoString) (c : w64) (s : List EtcdKv) : Prop :=
  ¬ HasKeyAt key c s ∧ ∀ v ∈ s, sint.Z c ≤ sint.Z v.createRev

/-- `key` is present in `s` with create revision `c` and value `val`. -/
def HasKeyValAt (key : GoString) (c : w64) (val : GoString) (s : List EtcdKv) : Prop :=
  ∃ v ∈ s, v.key = key ∧ v.createRev = c ∧ v.value = val

/-- The guard of `Proclaim` and `Resign`: `CreateRevision(key) = rev`. -/
def createGuard (key : GoString) (rev : w64) : CmpModel :=
  compareM (cmpKeyM .create key) .eq (.num rev)

/-- `Campaign`'s transaction: if `key` was never created, put it with the value `val` and the
lease; otherwise get it. -/
def campaignTxn (key val : GoString) (lease : w64) : TxnModel :=
  { cmps := [createGuard key (W64 0)], thenOps := [.put key val lease],
    elseOps := [.get (keyOp key)] }

/-- `Proclaim`'s transaction: if `key` still has create revision `rev`, put the value `val`. -/
def proclaimTxn (key : GoString) (rev : w64) (val : GoString) (lease : w64) : TxnModel :=
  { cmps := [createGuard key rev], thenOps := [.put key val lease], elseOps := [] }

/-- `Resign`'s transaction: if `key` still has create revision `rev`, delete it. -/
def resignTxn (key : GoString) (rev : w64) : TxnModel :=
  { cmps := [createGuard key rev], thenOps := [.delete (opDeleteModel key [])], elseOps := [] }

/-- **A successful `Proclaim`'s step**, at revision `r`, from the state `s0` (at `r - 1`) to `s`
(at `r`): the guard held on `s0`, and `s` is `s0` with `key` put (value `val`, the lease). -/
def ProclaimStep (key : GoString) (rev : w64) (val : GoString) (lease r : w64)
    (s0 s : List EtcdKv) : Prop :=
  cmpHolds s0 (createGuard key rev) = true ∧ s = putKv r key val lease s0

/-- **Only the leader's key is proclaimed** (pure): a successful `Proclaim` step with a positive
create revision `rev` (every `Campaign` makes one) happened on a state where `key` had create
revision `rev`, and leaves `key` with that create revision and the proclaimed value. -/
theorem proclaimStep_guard (key : GoString) (rev : w64) (val : GoString) (lease r : w64)
    (s0 s : List EtcdKv) (h : ProclaimStep key rev val lease r s0 s) (hrev : 0 < sint.Z rev) :
    HasKeyAt key rev s0 ∧ HasKeyValAt key rev val s := by
  obtain ⟨hc, rfl⟩ := h
  have hrev0 : rev ≠ W64 0 := by intro e; subst e; simp at hrev
  -- the guard's selection is not empty (a missing key compares as create revision `0`)
  have hsel : s0.filter (fun v => inRange key [] v.key) ≠ [] := by
    intro he
    simp only [cmpHolds, createGuard, compareM, cmpKeyM, he, ite_true] at hc
    simp [cmpKv, zeroKv, int64Cmp, cmpSign, CmpOp.holds] at hc
    by_cases h1 : 0 < sint.Z rev <;> by_cases h2 : W64 0 = rev <;> simp_all
  have hall : ∀ v ∈ s0, v.key = key → v.createRev = rev := by
    intro v hv hk
    simp only [cmpHolds, createGuard, compareM, cmpKeyM, hsel, ite_false, List.all_eq_true] at hc
    have := hc v (List.mem_filter.2 ⟨hv, by simp [inRange, hk]⟩)
    simp only [cmpKv, int64Cmp, cmpSign, CmpOp.holds] at this
    by_cases hlt : sint.Z v.createRev < sint.Z rev <;> by_cases heq : v.createRev = rev <;>
      simp_all
  obtain ⟨v, hv, hvk⟩ : ∃ v ∈ s0, v.key = key := by
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hsel
    rw [List.mem_filter] at hv
    exact ⟨v, hv.1, by simpa [inRange] using hv.2⟩
  refine ⟨⟨v, hv, hvk, hall v hv hvk⟩, ?_⟩
  obtain ⟨w, hw⟩ : ∃ w, s0.find? (fun v => decide (v.key = key)) = some w := by
    cases hf : s0.find? (fun v => decide (v.key = key)) with
    | some w => exact ⟨w, rfl⟩
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simpa using hvk) (hf v hv)
  have hwm := List.mem_of_find?_eq_some hw
  have hwk : w.key = key := by simpa using List.find?_some hw
  unfold putKv
  rw [hw]
  exact ⟨_, btInsert_self_mem _ _, hwk, hall w hwm hwk, rfl⟩

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-! ## The leader fact and what the methods return -/

/-- **`key` is the leader on `pfx` at revision `R`, created at `c`** (persistent): the mutex's
ownership fact (`lockedAt`). -/
def leaderAt (pfx key : GoString) (c R : w64) : IProp GF := lockedAt pfx key c R

instance leaderAt_persistent (pfx key : GoString) (c R : w64) :
    Persistent (leaderAt (GF := GF) pfx key c R) := by
  unfold leaderAt; infer_instance

/-- **A campaign that lost its key** (persistent): at `R`, under `pfx`, no key was created before
`c`, but `key` is not there with create revision `c` (`LostState`). -/
def campaignLost (pfx key : GoString) (c R : w64) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState R pfx s ∗ ⌜LostState key c s⌝)

instance campaignLost_persistent (pfx key : GoString) (c R : w64) :
    Persistent (campaignLost (GF := GF) pfx key c R) := by
  unfold campaignLost; infer_instance

/-- At revision `R`, `key` is present under `pfx` with create revision `c` and value `val`
(persistent). -/
def keyValAt (pfx key : GoString) (c : w64) (val : GoString) (R : w64) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState R pfx s ∗ ⌜HasKeyValAt key c val s⌝)

instance keyValAt_persistent (pfx key : GoString) (c : w64) (val : GoString) (R : w64) :
    Persistent (keyValAt (GF := GF) pfx key c val R) := by
  unfold keyValAt; infer_instance

/-- **`Proclaim`'s fact** (persistent): etcd's states at `r - 1` and `r` are a `ProclaimStep` of
`key` (guard: create revision `rev`) to the value `val` with the lease `lease`. -/
def proclaimedAt (pfx key : GoString) (rev : w64) (val : GoString) (lease r : w64) : IProp GF :=
  iprop(∃ s0 s : List EtcdKv, □ etcdState (r - W64 1) pfx s0 ∗ □ etcdState r pfx s ∗
    ⌜ProclaimStep key rev val lease r s0 s⌝)

instance proclaimedAt_persistent (pfx key : GoString) (rev : w64) (val : GoString) (lease r : w64) :
    Persistent (proclaimedAt (GF := GF) pfx key rev val lease r) := by
  unfold proclaimedAt; infer_instance

/-- At revision `R`, `key` is not present under `pfx` with create revision `c` (persistent): what a
failed guard, or a `Resign`, leaves. -/
def notLeaderAt (pfx key : GoString) (c R : w64) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState R pfx s ∗ ⌜¬ HasKeyAt key c s⌝)

instance notLeaderAt_persistent (pfx key : GoString) (c R : w64) :
    Persistent (notLeaderAt (GF := GF) pfx key c R) := by
  unfold notLeaderAt; infer_instance

/-- **The key-value `v` is the leader on `pfx` at `R`** (persistent; `LeaderKvState`). -/
def leaderKvAt (pfx : GoString) (v : EtcdKv) (R : w64) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState R pfx s ∗ ⌜LeaderKvState v s⌝)

instance leaderKvAt_persistent (pfx : GoString) (v : EtcdKv) (R : w64) :
    Persistent (leaderKvAt (GF := GF) pfx v R) := by
  unfold leaderKvAt; infer_instance

theorem leaderKvAt_leaderAt (pfx : GoString) (v : EtcdKv) (R : w64) :
    leaderKvAt (GF := GF) pfx v R ⊢ leaderAt pfx v.key v.createRev R := by
  unfold leaderKvAt leaderAt lockedAt
  iintro ⟨%s, #Hs, %Hl⟩
  iexists s
  iframe Hs
  ipureintro; exact Hl.locked

/-- **What an `Observe` response tells** (persistent): `v` is in etcd's state `s` at `R`, under
`pfx`, and
* it is the leader there (`v` created no later than any key); or
* `v`'s key was the leader at an earlier `R0`, created at `c0`, and has been re-created since: no
  key created before `c0` is left at `R` (a forwarded put the watch delivered without the delete
  before it); or
* the prefix was empty at an earlier `R0`, and every key at `R`, `v` too, was created after it (the
  first put after an empty prefix, or one forwarded from it).
With a watch that delivers every event (etcd's), the last two are the leader too; the client
contract does not promise that (`rangeWatchRespOk`), see `notes/decisions.md`. -/
def observedAt (pfx : GoString) (v : EtcdKv) (R : w64) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState R pfx s ∗ ⌜v ∈ s⌝ ∗
    (⌜∀ w ∈ s, sint.Z v.createRev ≤ sint.Z w.createRev⌝ ∨
     (∃ c0 R0 : w64, lockedAt pfx v.key c0 R0 ∗
        ⌜sint.Z R0 < sint.Z R ∧ sint.Z c0 < sint.Z v.createRev ∧
          ∀ w ∈ s, sint.Z c0 ≤ sint.Z w.createRev⌝) ∨
     (∃ R0 : w64, □ etcdState R0 pfx [] ∗
        ⌜sint.Z R0 < sint.Z R ∧ ∀ w ∈ s, sint.Z R0 < sint.Z w.createRev⌝)))

instance observedAt_persistent (pfx : GoString) (v : EtcdKv) (R : w64) :
    Persistent (observedAt (GF := GF) pfx v R) := by
  unfold observedAt; infer_instance

theorem leaderKvAt_observedAt (pfx : GoString) (v : EtcdKv) (R : w64) :
    leaderKvAt (GF := GF) pfx v R ⊢ observedAt pfx v R := by
  unfold leaderKvAt observedAt
  iintro ⟨%s, #Hs, %Hl⟩
  iexists s
  iframe Hs
  isplitr
  · ipureintro; exact Hl.1
  ileft; ipureintro; exact Hl.2

/-- The `*GetResponse` `resp` lists one `*KeyValue`, `kp`, holding `v` (read-only). -/
def getRespOneKv (resp kp : Loc) (v : EtcdKv) : IProp GF :=
  iprop(∃ sl : GoSlice, structFieldRef go_etcd_io.etcd.client.v3.GetResponse go!"Kvs" resp ↦□ sl ∗
    sl ↦*□ [kp] ∗ kvValAt kp v)

instance getRespOneKv_persistent (resp kp : Loc) (v : EtcdKv) :
    Persistent (getRespOneKv (GF := GF) resp kp v) := by
  unfold getRespOneKv; infer_instance

/-! ## `Observe`'s channel -/

/-- The ghost names of an `Observe` channel: the channel's (SPSC: `observe` produces, the caller
consumes) and the revisions of its responses' facts (a monotone list, `Observe`'s `lo` first). -/
structure ObserveNames where
  spsc : SpscNames
  revs : GName

/-- **One response of `Observe`** (persistent): a `*GetResponse` with a header (whose revision is
the get's, the first put's, or the watch response's, and is not otherwise constrained) and one
key-value `v`, which `observedAt pfx v R`. -/
def observeResp (pfx : GoString) (resp : Loc) (R : w64) : IProp GF :=
  iprop(∃ (hdr : Loc) (Rh : w64) (kp : Loc) (v : EtcdKv),
    structFieldRef go_etcd_io.etcd.client.v3.GetResponse go!"Header" resp ↦□ hdr ∗ ⌜hdr ≠ null⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ Rh ∗
    getRespOneKv resp kp v ∗ observedAt pfx v R)

instance observeResp_persistent (pfx : GoString) (resp : Loc) (R : w64) :
    Persistent (observeResp (GF := GF) pfx resp R) := by
  unfold observeResp; infer_instance

/-- The `i`-th response of an `Observe` channel: its fact's revision `R`, at least the previous
response's (`γ.revs`, from `Observe`'s `lo`), reached by etcd. -/
def observeElem (γ : ObserveNames) (pfx : GoString) (i : Int) (resp : Loc) : IProp GF :=
  iprop(∃ Rp R : w64, monoListIdxOwn γ.revs i.toNat Rp ∗ monoListIdxOwn γ.revs (i.toNat + 1) R ∗
    ⌜sint.Z Rp ≤ sint.Z R⌝ ∗ etcdReached R ∗ observeResp pfx resp R)

instance observeElem_persistent (γ : ObserveNames) (pfx : GoString) (i : Int) (resp : Loc) :
    Persistent (observeElem (GF := GF) γ pfx i resp) := by
  unfold observeElem; infer_instance

/-- **`Observe`'s channel** `ch` (persistent): an SPSC channel of `observeElem`s, closed with no
promise (`True`). -/
def isObserveChan (ch : Loc) (γ : ObserveNames) (pfx : GoString) : IProp GF :=
  isSpsc γ.spsc ch (observeElem γ pfx) (fun _ => iprop(True))

instance isObserveChan_persistent (ch : Loc) (γ : ObserveNames) (pfx : GoString) :
    Persistent (isObserveChan (GF := GF) ch γ pfx) := by
  unfold isObserveChan; infer_instance

/-! ## The election -/

/-- The fields of an `Election` its methods write: the leader key, its create revision, the
leader session (nil or the election's session), the response header of the last campaign or
proclamation. -/
structure ElectionSt where
  key : GoString
  rev : w64
  sess : Loc
  hdr : Loc

/-- `NewElection`'s state: every field zero. -/
def ElectionSt.init : ElectionSt := { key := [], rev := W64 0, sess := null, hdr := null }

/-- **The election's state** (exclusive): its fields `leaderKey`, `leaderRev`, `leaderSession`,
`hdr` hold `st`; `leaderSession` is nil or the session `s`. -/
def electionState (e s : Loc) (st : ElectionSt) : IProp GF :=
  iprop(structFieldRef Election go!"leaderKey" e ↦ st.key ∗
    structFieldRef Election go!"leaderRev" e ↦ st.rev ∗
    structFieldRef Election go!"leaderSession" e ↦ st.sess ∗
    structFieldRef Election go!"hdr" e ↦ st.hdr ∗ ⌜st.sess = null ∨ st.sess = s⌝)

/-- **The election** `e` (persistent): its session `s` (of `client`, with the lease `id`) and its
key prefix `pfx` (`NewElection`'s argument with a `/`, `ResumeElection`'s as given), read-only,
and the client's contract for `pfx`. -/
def isElection (e s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString) :
    IProp GF :=
  iprop(structFieldRef Election go!"session" e ↦□ s ∗
    structFieldRef Election go!"keyPrefix" e ↦□ pfx ∗
    ⌜pfx ≠ []⌝ ∗ isSession s γ client id ∗ isEtcdMutexClient client pfx)

instance isElection_persistent (e s : Loc) (γ : SessionNames) (client : Loc) (id : w64)
    (pfx : GoString) : Persistent (isElection (GF := GF) e s γ client id pfx) := by
  unfold isElection; infer_instance

end defs

end concurrency
end EtcdGrove
end Perennial
