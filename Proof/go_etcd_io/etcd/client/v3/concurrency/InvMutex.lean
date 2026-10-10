/-
`client/v3/concurrency`'s `Mutex` (`mutex.go`, `key.go`): the vocabulary of
`Spec/go_etcd_io/etcd/client/v3/concurrency/{NewMutex,Mutex__*,NewLocker,waitDelete,waitDeletes}.lean`
and **mutual exclusion**. Lean-first (no Rocq counterpart). See `decisions.md`, "Mutex: `lockedAt`,
exclusion from the two history laws".

**The protocol.** A mutex on the prefix `pfx` (the field `m.pfx`, `NewMutex`'s argument with a
`/`) puts the key `pfx ++ hex(lease)` with its session's lease, in a transaction that creates it
only if it does not exist (`tryAcquire`); the key with the smallest create revision under `pfx`
holds the lock; a waiter waits until every key created before its own is deleted (`waitDeletes`,
`waitDelete`), and checks its own key is still there.

**The ownership fact** `lockedAt pfx key c R` (persistent): at revision `R`, under `pfx`, `key` is
present with create revision `c`, and every key present has a create revision at least `c`
(`LockedState`). `TryLock` and `Lock` return it (`Lock` possibly the weaker `keyRecreated`, see its
spec). **Mutual exclusion** (`lockedAt_exclusion`): two holders `(k1, c1)`, `(k2, c2)` with
`c1 ≠ c2` are never both present in a state at a revision at or after both `R`s. From the two
history laws only (`etcdState_revs`, `etcdState_create_persist`): if both were present at `a`, the
one created first (say `c1 < c2`) was present at `R2` (its creation `c1 < c2 ≤ R2 ≤ a`), with a
create revision below `c2`, against `lockedAt k2 c2 R2`'s minimality.

**The client** (`isEtcdMutexClient client pfx`, persistent): its `KV` answers gets (`isEtcdKV`,
with the range clause `getRespRange`), transactions (`isEtcdTxnKV`) and deletes
(`isEtcdDeleteKV`), its `Watcher` single-key watches (`isEtcdKeyWatcher`), all for the prefix
`pfx`; its context field holds a context (`client.Ctx()`, which `Lock` passes to `Unlock`).

**The mutex** (`isMutex m s γ client id pfx`, persistent: its session `s` and prefix `pfx` never
change; the session's client and lease) and its **state** (`mutexState m st`, exclusive: `myKey`,
`myRev`, `hdr`, which `TryLock`, `Lock`, `Unlock` write). A record, not an enumeration of
"unlocked/locked/released": an error leaves the fields part-way (`tryAcquire` writes `myKey`
before its transaction), and every method runs from any state.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSession
public import Proof.go_etcd_io.etcd.cache.v3.InvNew

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

/-! ## The ownership fact and mutual exclusion (pure) -/

/-- The state `s` has the key `key` with create revision `c`. -/
def HasKeyAt (key : GoString) (c : w64) (s : List EtcdKv) : Prop :=
  ∃ v ∈ s, v.key = key ∧ v.createRev = c

/-- In the state `s`, `key` holds the lock with create revision `c`: it is present with that create
revision, and no key has a smaller one. -/
def LockedState (key : GoString) (c : w64) (s : List EtcdKv) : Prop :=
  HasKeyAt key c s ∧ ∀ v ∈ s, sint.Z c ≤ sint.Z v.createRev

/-- `myKey` was re-created: present with a create revision above `c`, and no key has a create
revision below `c` (what `Lock`'s final check, which only asks that the key exist, cannot tell
from `LockedState key c s`). -/
def RecreatedState (key : GoString) (c : w64) (s : List EtcdKv) : Prop :=
  (∃ v ∈ s, v.key = key ∧ sint.Z c < sint.Z v.createRev) ∧ ∀ v ∈ s, sint.Z c ≤ sint.Z v.createRev

/-- The get `OpGet(pfx, WithFirstCreate()...)` of `tryAcquire` (the owner). -/
def ownerOp (pfx : GoString) : OpFull := opGetModel pfx (withTopM (W64 2) (W64 1))

/-- The get `OpGet(pfx, WithLastCreate()..., WithMaxCreateRev(n))` of `waitDeletes`. -/
def lastCreateOp (pfx : GoString) (n : w64) : OpFull :=
  opGetModel pfx (withTopM (W64 2) (W64 2) ++ [withMaxCreateRevM n])

/-- The get `OpGet(key)` (a single key, no options). -/
def keyOp (key : GoString) : OpFull := opGetModel key []

/-- `tryAcquire`'s transaction: if `myKey` was never created, put it (with the lease) and get the
owner; otherwise get `myKey` and the owner. -/
def acquireTxn (pfx key : GoString) (lease : w64) : TxnModel :=
  { cmps := [compareM (cmpKeyM .create key) .eq (.num (W64 0))],
    thenOps := [.put key [] lease, .get (ownerOp pfx)],
    elseOps := [.get (keyOp key), .get (ownerOp pfx)] }

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-! ## The ownership fact -/

/-- **`key` holds the lock on `pfx` at revision `R`, created at `c`** (persistent): etcd's state
at `R` under `pfx` is `LockedState key c`. -/
def lockedAt (pfx key : GoString) (c R : w64) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState R pfx s ∗ ⌜LockedState key c s⌝)

instance lockedAt_persistent (pfx key : GoString) (c R : w64) :
    Persistent (lockedAt (GF := GF) pfx key c R) := by
  unfold lockedAt; infer_instance

/-- `key`, which had create revision `c`, was deleted and re-created before `R`, with no key
created before `c` left at `R` (persistent; see `RecreatedState`). -/
def keyRecreated (pfx key : GoString) (c R : w64) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState R pfx s ∗ ⌜RecreatedState key c s⌝)

instance keyRecreated_persistent (pfx key : GoString) (c R : w64) :
    Persistent (keyRecreated (GF := GF) pfx key c R) := by
  unfold keyRecreated; infer_instance

/-- One direction of exclusion: a holder `(k2, c2)` at `R2` excludes, at any `a ≥ R2`, a key `k1`
created before `c2`. -/
theorem lockedAt_excludes_earlier (pfx k1 k2 : GoString) (c1 c2 R2 a : w64) (s : List EtcdKv)
    (hc : sint.Z c1 < sint.Z c2) (ha : sint.Z R2 ≤ sint.Z a) :
    lockedAt (GF := GF) pfx k2 c2 R2 ∗ etcdState a pfx s ⊢ ⌜¬ HasKeyAt k1 c1 s⌝ := by
  unfold lockedAt
  iintro ⟨⟨%s2, #Hs2, %Hl⟩, Hs⟩
  ihave %Hrevs := etcdState_revs R2 pfx s2 $$ Hs2
  ihave %Hp := etcdState_create_persist a R2 pfx s s2 $$ [$Hs $Hs2]
  ipureintro
  rintro ⟨v, hv, hk, hc1⟩
  obtain ⟨⟨w, hw, -, hwc⟩, hmin⟩ := Hl
  have hc2R : sint.Z c2 ≤ sint.Z R2 := by
    have := Hrevs w hw; rw [hwc] at this; omega
  obtain ⟨v', hv', -, hv'c⟩ := Hp v hv (by rw [hc1]; omega) ha
  have := hmin v' hv'
  rw [hv'c, hc1] at this
  omega

/-- **Mutual exclusion**: two holders of the lock on `pfx`, `(k1, c1)` at `R1` and `(k2, c2)` at
`R2`, with different create revisions, are never both present in etcd's state at a revision `a`
at or after both `R1` and `R2`. -/
theorem lockedAt_exclusion (pfx k1 k2 : GoString) (c1 c2 R1 R2 a : w64) (s : List EtcdKv)
    (hne : c1 ≠ c2) (h1 : sint.Z R1 ≤ sint.Z a) (h2 : sint.Z R2 ≤ sint.Z a) :
    lockedAt (GF := GF) pfx k1 c1 R1 ∗ lockedAt pfx k2 c2 R2 ∗ etcdState a pfx s ⊢
      ⌜¬ (HasKeyAt k1 c1 s ∧ HasKeyAt k2 c2 s)⌝ := by
  iintro ⟨#H1, #H2, Hs⟩
  have hz : sint.Z c1 ≠ sint.Z c2 := fun h => hne (by word)
  rcases Int.lt_or_gt_of_ne hz with hlt | hgt
  · ihave %H := lockedAt_excludes_earlier pfx k1 k2 c1 c2 R2 a s hlt h2 $$ [$H2 $Hs]
    ipureintro; exact fun ⟨h, _⟩ => H h
  · ihave %H := lockedAt_excludes_earlier pfx k2 k1 c2 c1 R1 a s hgt h1 $$ [$H1 $Hs]
    ipureintro; exact fun ⟨_, h⟩ => H h

/-! ## The client -/

/-- **The client, as a mutex uses it** (persistent; see the module docstring): for the prefix
`pfx`, gets, transactions and deletes through its `KV`, single-key watches through its `Watcher`,
and a context in its `ctx` field. The trust boundary about the client (definitions, as
`isEtcdClient`). -/
def isEtcdMutexClient (client : Loc) (pfx : GoString) : IProp GF :=
  iprop(∃ (kv w cctx : GoInterfaceOk) (ccs : context.ContextDesc (IProp GF)),
    clientKVAddr client ↦□ GoInterface.ok kv ∗ clientWatcherAddr client ↦□ GoInterface.ok w ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" client ↦□ GoInterface.ok cctx ∗
    context.isContext cctx ccs ∗
    isEtcdKV kv pfx ∗ isEtcdTxnKV kv pfx ∗ isEtcdDeleteKV kv pfx ∗ isEtcdKeyWatcher w pfx)

instance isEtcdMutexClient_persistent (client : Loc) (pfx : GoString) :
    Persistent (isEtcdMutexClient (GF := GF) client pfx) := by
  unfold isEtcdMutexClient; infer_instance

/-! ## The mutex -/

/-- The fields of a `Mutex` its methods write: the key, its create revision (`-1`: none), the
response header of the last acquisition. -/
structure MutexSt where
  key : GoString
  rev : w64
  hdr : Loc

/-- `NewMutex`'s state: `myKey = ""`, `myRev = -1`, `hdr = nil`. -/
def MutexSt.init : MutexSt := { key := [], rev := W64 (-1), hdr := null }

/-- The state after `Unlock` (or `TryLock`'s `ErrLocked`): `myKey = "\x00"`, `myRev = -1`. -/
def MutexSt.released (hdr : Loc) : MutexSt := { key := go!"\x00", rev := W64 (-1), hdr := hdr }

/-- `Unlock`'s check: the mutex holds no key (`ErrLockReleased`). -/
def MutexSt.noKey (st : MutexSt) : Prop :=
  st.key = [] ∨ sint.Z st.rev ≤ 0 ∨ st.key = go!"\x00"

/-- **The mutex's state** (exclusive): its fields `myKey`, `myRev`, `hdr` hold `st`. -/
def mutexState (m : Loc) (st : MutexSt) : IProp GF :=
  iprop(structFieldRef Mutex go!"myKey" m ↦ st.key ∗ structFieldRef Mutex go!"myRev" m ↦ st.rev ∗
    structFieldRef Mutex go!"hdr" m ↦ st.hdr)

/-- **The mutex** `m` (persistent): its session `s` (of `client`, with the lease `id`) and its
prefix `pfx` (with `NewMutex`'s `/`), read-only, and the client's contract for `pfx`. -/
def isMutex (m s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString) :
    IProp GF :=
  iprop(structFieldRef Mutex go!"s" m ↦□ s ∗ structFieldRef Mutex go!"pfx" m ↦□ pfx ∗
    ⌜pfx ≠ []⌝ ∗ isSession s γ client id ∗ isEtcdMutexClient client pfx)

instance isMutex_persistent (m s : Loc) (γ : SessionNames) (client : Loc) (id : w64)
    (pfx : GoString) : Persistent (isMutex (GF := GF) m s γ client id pfx) := by
  unfold isMutex; infer_instance

/-- The response header `hdr` (non-nil) has revision `r`, read-only. -/
def hdrRevAt (hdr : Loc) (r : w64) : IProp GF :=
  iprop(⌜hdr ≠ null⌝ ∗ structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ r)

instance hdrRevAt_persistent (hdr : Loc) (r : w64) : Persistent (hdrRevAt (GF := GF) hdr r) := by
  unfold hdrRevAt; infer_instance

/-- The error `err` is the package variable `x`'s (`ErrLocked`, ...). -/
def isPkgErr (x : GoString) (err : GoInterface) : IProp GF :=
  iprop(globalAddr x ↦□ err ∗ ⌜err ≠ GoInterface.nil⌝)

instance isPkgErr_persistent (x : GoString) (err : GoInterface) :
    Persistent (isPkgErr (GF := GF) x err) := by
  unfold isPkgErr; infer_instance

/-- **`tryAcquire`'s response** `resp` (a `*TxnResponse`, read-only), for the mutex's prefix
`pfx`, key `key` and create revision `rev`: its header `hdr` has revision `r`; etcd's state `s`
at `r` (after the transaction) has `key` with create revision `rev`; and `Responses[1]` is the
owner get's response (`ownerOp`) on `s`. -/
def acquireResp (resp : Loc) (pfx key : GoString) (rev r : w64) (hdr : Loc) : IProp GF :=
  iprop(∃ (s : List EtcdKv) (rsl : GoSlice) (ps : List Loc) (p : Loc) (n : Nat),
    structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ hdr ∗ hdrRevAt hdr r ∗
    □ etcdState r pfx s ∗ ⌜EtcdStateWf pfx s ∧ HasKeyAt key rev s⌝ ∗
    structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ rsl ∗ rsl ↦*□ ps ∗
    ⌜ps[1]? = some p⌝ ∗
    txnOpRespAt p (.get (ownerOp pfx)) (.range (rangeSel s (ownerOp pfx)) n))

instance acquireResp_persistent (resp : Loc) (pfx key : GoString) (rev r : w64) (hdr : Loc) :
    Persistent (acquireResp (GF := GF) resp pfx key rev r hdr) := by
  unfold acquireResp; infer_instance

end defs

end concurrency
end EtcdGrove
end Perennial
