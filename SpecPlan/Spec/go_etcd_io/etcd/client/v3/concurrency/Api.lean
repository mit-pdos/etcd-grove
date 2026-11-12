/-
# `client/v3/concurrency`: the vocabulary (batch 1d)

Sessions (a lease kept alive), mutexes and elections (keys under a prefix, ordered by create
revision), and software transactional memory (an attempt's reads validated by mod revision at
commit), over the client's contract (`client/v3/Api.lean`, W0) and the cluster's model
(`api/v3/Model.lean`: `State`, `Step`, `Reach`; `State.lean`: `etcdState`, `etcdLb`).

## What the package can promise without a time model

W0's model has no time: a lease may expire at any moment (`EnvStep.leaseExpire`), and a keep-alive
promises nothing. So nothing here is about time: a `Session` promises a lease that was granted
(or the one the caller named), not one that is alive; a `Mutex` promises **exclusion of
revisions**, not of time. The guarantees are:

* **Mutex** (`lockedSince`, `fence`): when `Lock` returns `nil`, at a state `σ` reached after the
  state `σ0` the caller knew (every spec that returns a state takes the caller's `etcdLb γ σ0` and
  returns `Reach σ0 σ`), no key under the prefix is older than the mutex's own create revision `c`
  (`noOlder`), and the header it keeps is `σ`'s revision. Any later state at which the mutex's key
  still has create revision `c` (what `IsOwner()`, `CreateRevision(key) = c`, compares) is one at
  which the key is the oldest under the prefix (`holdsAt`): the pure law `fence`. So a write (or a
  linearizable read) fenced by `Txn(If(m.IsOwner()))` (W0's transaction contract) takes effect only
  in a state where the mutex holds the lock, and two holders' fenced writes never take effect in
  one state. A read-only transaction of serializable ranges is answered at a member's possibly
  stale view: its fence proves nothing now. This holds even of `Lock`'s known gap
  (`issues/mutex-lock-recreated.md`): the fence then fails, as it should. A mutex (an election)
  writes only its session's key (`sessKey pfx lease`, `mutexEff`, `campaignEff`), so with W0's
  `EnvCfg.leaseExpiry = false` (no key deleted but by its owner) a holder's key stays until its
  `Unlock`, and a later locker's `lockedSince` excludes it: **time exclusion** between the
  holders of distinct sessions (snippets `ReqMutexNoTwoHolders`, `ReqElectionNoTwoLeaders`; verify-round
  A3 completeness F2; the sessions' leases distinct by `NewSession.spec`'s grant pre-state).
* **Election**: `Campaign` gives the wait's fact at its create revision (`waitedFor`, without the
  last check: `nonissues/election-campaign-key-check.md`); `Proclaim` and `Resign` are fenced by
  the comparison `CreateRevision(leaderKey) = leaderRev` and say whether it held (as W0's
  `Compare.holds` decides: at revision `0` an absent key passes,
  `nonissues/etcd-v3election-proclaim-rev-zero.md`); `Leader` returns the oldest key under the
  prefix at a linearized read (`holdsAt`); `Observe`'s values were each the oldest key's write at
  some revision (`ObservedAt`), with no order between headers; the values that come from the
  watch are known only under the compaction condition (W0's `exactFrom`: no revision from the
  observer's start up to the compaction revision changes a key twice), as 1b's watch states it.
* **STM** (`stmCommitted`): the committed attempt's writes were applied in one revision at a state
  `σ`, and (`SerializableSnapshot`, `Serializable`, `RepeatableReads`) every read of the attempt is
  `σ`'s key-value of its key: the attempt ran atomically at `σ` (serializability). A
  `RepeatableReads` attempt that wrote nothing is checked by a serializable transaction, so `σ` is
  then a past revision (`issues/etcd-txn-empty-serializable.md`). `SerializableSnapshot` also: no
  written key was modified after the attempt's first read. `ReadCommitted`: each read is some
  revision's. A failed attempt's reads promise nothing (`issues/stm-serializable-snapshot.md`);
  during an attempt, each read is some reached revision's (`stmAt_reads`).

## The permission: how the package changes the cluster's state

The package's functions make many requests per call (a lock's transaction, the gets and watches
of its wait, its cleanup delete; an STM's reads and failed commits). Each spec states the
transitions it may cause as a pure relation (`mutexEff`, `campaignEff`, `putEff`, `delEff`,
`grantEff`, `revokeEff`, `stmEff`; reads change nothing) and requires it to be included in the
caller's `T`: the caller's own invariant over `etcdState` must be stable under `T`. The effects are
stated in the model's terms, never as the requests the code sends. Facts come back as `etcdLb γ σ`
with pure model predicates.

**Lent per call** (round 1, the coordinator's choice): the KV writes of a mutex, an election and an
STM take **`etcdLent γ T P ∗ P`**: W0's `etcdPeek` for the reads, and an update performing `T` that
can be fired only by giving up the caller's token `P`, back at its commit. The call returns `P` on
every outcome whose writes have all been answered (success, `ErrLocked`, `ErrSessionExpired`,
`ErrElectionNotLeader`, `ErrLockReleased`, ...); an outcome after which a write may still be pending
(an indefinite error) keeps it. While the caller holds `P`, the package changes nothing, so a
caller can rely on its keys' contents between calls. With `P := True` it is round 0's persistent
permission. The session's grant and revoke take W0's persistent **`etcdPerm γ T`**: they are
repeatable calls (retried after `Unavailable`), so an earlier attempt may apply after the call has
answered; no token can be given back for them. Alternative (open question in `batch-1d.md`): one
persistent permission for everything, simpler to give and weaker to rely on.

**W0's read window and validation** (integration I1): every read the package sends through W0's
KV contract (`KV.GetTriple`, `Txn.CommitTriple`) is given `lo := 0` (`authLb γ 0` holds by its left
disjunct): the package's facts are about the data a read returns, never about the auth state its
check saw, so the weakest window suffices. Its transactions are valid and put each key at most once
per path (`kvStep`'s `t.valid` and `putOnce`: non-empty keys under `pfx + "/"`, one put per key of
the STM's write set); in any case an invalid one is only refused, which every spec's generic error
disjunct covers, since no spec promises a write's success.

**The principal per call**: a session names its client (`isSession s c γ id`); each mutex and
election method takes `isClient c γ dflt` (the client's default principal) and its context's
`ctxPrin dflt ctx who`, the call's principal `who` (W0's round 3; the in-process client
of v3lock/v3election sends each request as the RPC's principal); cleanups that run on
`client.Ctx()` run as the client's own principal (`Client.Ctx.spec`, 1c).

## Vocabulary

Pure (transparent): `noOlder`, `holdsAt`, `firstCreate`, `waitedFor`, `lockedSince`,
`ObservedAt`; the effects `putKey`, `delKey`, `putEff`, `delEff`, `mutexEff`, `campaignEff`,
`grantEff`, `revokeEff`, `readEff`, `effIn`; the options' models (`SessOpts`, `STMOpts`) and the
STM's attempt (`Attempt`: `ReadM`, `WriteM`, `readOf`, `readsAgree`, `readsSeen`, `applied`,
`stmCommitted`, `stmEff`, `GetPost`, `RevPost`); the package's errors (`ConcErr`, `concErrsOk`); the session's key
`sessKey`; the mutex's and the election's fields (`MutexSt`, `ElectionSt`), `ownerCmp`.

Resources:
* `etcdLent γ T P` (transparent): the lent permission above; W0's `etcdPerm`, `etcdPeek`.
* `isSession s c γ id` (persistent): `s` is a `*Session` over the client `c` of `γ` with lease
  `id`; its fields read-only. Intended realization: the fields `↦□`, the options' context (`ctxOk`,
  `ctxPrin` of the principal it was made as, with that principal's `clientRest`: `NewSession`
  takes no more, the gRPC proxy's client having its `KV` field replaced), the `donec`
  broadcast channel (Perennial's `ownBroadcastChan ch γc True`), the cancel function's spec.
* `sessOptAt f g` (persistent): the `SessionOption` closure `f` changes the options as `g`
  (`sessOptsAt` a read-only slice of them); `optCtxOk o who` the options' context, if set, a
  context of `who`. Same for `stmOptAt`/`stmOptsAt`.
* `isMutex m s pfx` (persistent: the fields `s` and `pfx`, read-only) and `mutexSt m st`
  (exclusive: `myKey`, `myRev`, `hdr`). `isElection e s pfx` / `electionSt e st` the same for
  an `Election` (`Observe`'s goroutine reads `session` and `keyPrefix` while the caller keeps
  using the election).
* `observeAt ch γ pfx σ0` (exclusive): the consumer of `Observe`'s channel, its values read after
  `σ0`. Intended realization: Perennial's single-producer single-consumer channel (`isSpsc`,
  `spscConsumer`) with `observe` the producer (`observeProd`, internal).
* `stmAt iv γ who iso a` (exclusive) and `stmStale iv γ who iso` (between attempts): the `STM`
  interface value `iv` (level `iso`) holding the attempt `a`; its methods' triples are the law
  `stmAt_methods` (`Get`, `Put`, `Rev`, `Del`: the user's closure's view; `commit`, `reset`: the
  package's own). Intended realization: a bundle over `stmCoreAt`/`stmSerAt` (internal) and `etcdPeek`.
* `applyOk apply γ who F Rel` (persistent): the user's closure `apply` meets the STM's contract: on
  any `stmAt` of an attempt with no writes yet, it returns an error, or `nil` with an attempt
  satisfying `Rel`, keeping the caller's frame `F` (indexed by the attempt), or aborts through a
  method (`stmRet`). `stmResult` (def) is `NewSTM`'s outcome.
* Internal (the package's own proofs; no client mentions them): `observeProd`, `stmCoreAt`,
  `stmCoreStale`, `stmSerAt`, `stmSerStale`, `readSetAt`, `writeSetAt`, `readRespAt`.

## Laws

`fence` (pure: the fencing guarantee); `init.spec` (the package's error variables, their values
existential: `concErrs`, `concErrsOk`; with W0's `callErr_errorsNew`, no client call's error is
one of them; `notConcErr` a definition); `handles_persistent`; `isSession_client`; `sessOptAt_call`, `stmOptAt_call`;
`electionSt_session`; `observeAt_recv`, `observeAt_recvAu`; `stmAt_methods`, `stmAt_reads`;
`applyOk_persistent`.

## Requirement snippets

`examples/specreq/concurrency/`: `session.go` (`ReqSessionLease`, `ReqSessionResumeLease`,
`ReqSessionDone`, `ReqSessionClose`, `ReqSessionTTL`), `mutex.go` (`ReqFencedWrite`: the fence;
`ReqV3LockPattern`, `ReqTryLock`, `ReqLockUnlock`, `ReqLocker`, `ReqLockAfterUnlock`,
`ReqMutexNoTwoHolders`: time exclusion with no lease expiry), `election.go`
(`ReqCampaignProclaim`, `ReqResumedProclaim`, `ReqLeader`, `ReqLeaderFenced`, `ReqObserve`,
`ReqElectionNoTwoLeaders`: time exclusion of leaders),
`stm.go` (`ReqSTMTransfer`: serializability keeps an invariant; `ReqSTMLevels`,
`ReqSTMRepeatable`, `ReqSTMPrefetch`, `ReqSTMAbort`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.v3.concurrency
public import SpecPlan.Spec.PkgInit.go_etcd_io.etcd.client.v3.concurrency
public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api
public import SpecPlan.Spec.go_uber_org.zap.Api
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Concurrency

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

/-! ## Keys under a prefix, ordered by create revision -/

/-- A key-value's record (`KV` without its key). -/
def recOf (v : KV) : KeyRec :=
  { createRev := v.createRev, modRev := v.modRev, version := v.version, value := v.value,
    lease := v.lease }

/-- **No key under `pfx` in the store `s` is older than `c`** (has a create revision below `c`). -/
def noOlder (pfx : GoString) (c : Nat) (s : EtcdModel.Store) : Prop :=
  ∀ k r, pfx <+: k → s k = some r → c ≤ r.createRev

/-- **`k`, created at `c`, is the oldest key under `pfx` in `s`** (the lock's or the election's
holder there; keys created by one transaction share a create revision, so two keys may both be). -/
def holdsAt (pfx k : GoString) (c : Nat) (s : EtcdModel.Store) : Prop :=
  pfx <+: k ∧ (∃ r, s k = some r ∧ r.createRev = c) ∧ noOlder pfx c s

/-- `l` is what `Get(pfx, WithFirstCreate()...)` answers at `s`: nothing if no key is under `pfx`,
else one key-value, of an oldest key. -/
def firstCreate (pfx : GoString) (s : EtcdModel.Store) (l : List KV) : Prop :=
  (l = [] ∧ ∀ k, pfx <+: k → s k = none) ∨
  ∃ v, l = [v] ∧ pfx <+: v.key ∧ s v.key = some (recOf v) ∧ noOlder pfx v.createRev s

/-- **The wait's fact** (`waitDeletes`, `Election.Campaign`): `k` is under `pfx`, `c` is a
positive revision `σ` has reached, and no key under `pfx` is older than `c` at `σ`. With `fence`,
any later state where `k`'s create revision is `c` is one where `k` holds (`holdsAt`). -/
def waitedFor (pfx k : GoString) (c : Nat) (σ : State) : Prop :=
  pfx <+: k ∧ 0 < c ∧ c ≤ σ.kv.rev ∧ noOlder pfx c σ.kv.store

/-- **The lock fact** (`Mutex.Lock`): the wait's, and `k` present at `σ` with a create revision
at least `c` (`c` itself unless `k` was re-created meanwhile: `issues/mutex-lock-recreated.md`). -/
def lockedSince (pfx k : GoString) (c : Nat) (σ : State) : Prop :=
  waitedFor pfx k c σ ∧ ∃ r, σ.kv.store k = some r ∧ c ≤ r.createRev

/-- **An observed leader value** (`Election.Observe`) in the history `h`: `v` (under `pfx`) was
written by an event of its mod revision, and at some revision from that one on no key under `pfx`
was older than `v`'s create revision. -/
def ObservedAt (pfx : GoString) (v : KV) (h : KVHist) : Prop :=
  pfx <+: v.key ∧ v.modRev ≤ h.rev ∧ Event.put v.key (recOf v) ∈ h.eventsAt v.modRev ∧
  ∃ r, v.modRev ≤ r ∧ r ≤ h.rev ∧ noOlder pfx v.createRev (h.storeAt r)

/-! ## The package's effects on the cluster's state -/

/-- `k` put to `v` with `lease` (a plain put: its create revision kept if present). -/
def putKey (σ : State) (k v : Bytes) (lease : Int) : State :=
  σ.withKV (σ.kv.commit [.put k
    (({ key := k, value := v, lease := lease, prevKv := false, ignoreValue := false,
        ignoreLease := false } : PutReq).record (σ.kv.rev + 1) (σ.kv.store k))])

/-- `k` deleted (no revision if it is absent). -/
def delKey (σ : State) (k : Bytes) : State :=
  σ.withKV (σ.kv.commit (if σ.kv.store k = none then [] else [.delete k]))

/-- A read: no change. -/
def readEff (σ σ' : State) : Prop := σ' = σ

/-- **Puts the package makes**: nothing, or a key satisfying `ks` put to a value satisfying `vs`
with the lease `lease` (a plain put: a present key keeps its create revision). -/
def putEff (ks : Bytes → Prop) (vs : Bytes → Prop) (lease : Int) (σ σ' : State) : Prop :=
  σ' = σ ∨ ∃ k v, ks k ∧ vs v ∧ σ' = putKey σ k v lease

/-- **Deletes the package makes**: nothing, or a key satisfying `ks` deleted. -/
def delEff (ks : Bytes → Prop) (σ σ' : State) : Prop :=
  σ' = σ ∨ ∃ k, ks k ∧ σ' = delKey σ k

/-- **The session's key under `pfx`**: `fmt.Sprintf("%s%x", pfx, lease)` (Perennial's `%x`: the
lowercase hexadecimal, `-` before a negative one), the key a mutex or a campaign of a session with
lease `lease` writes (`tryAcquire`, `Campaign`). -/
def sessKey (pfx : GoString) (lease : Int) : GoString := pfx ++ Perennial.fmt.hexadecimal lease

/-- **A mutex's writes** (`Lock`, `TryLock`): the session's key under `pfx` created empty with the
session's lease, or deleted (the cleanup `Unlock`). Only that key (verify-round A3 completeness F2:
a mutex never touches another session's key, so a caller's invariant that another holder's key
stays present is stable under it). -/
def mutexEff (pfx : GoString) (lease : Int) (σ σ' : State) : Prop :=
  putEff (fun k => k = sessKey pfx lease) (fun v => v = []) lease σ σ' ∨
    delEff (fun k => k = sessKey pfx lease) σ σ'

/-- **A campaign's writes**: the session's key under `pfx` put to `val` with the session's lease
(created, or proclaimed), or deleted (the cleanup `Resign`); only that key, as `mutexEff`. -/
def campaignEff (pfx val : GoString) (lease : Int) (σ σ' : State) : Prop :=
  putEff (fun k => k = sessKey pfx lease) (fun v => v = val) lease σ σ' ∨
    delEff (fun k => k = sessKey pfx lease) σ σ'

/-- **A lease granted** (`NewSession`): nothing, or a lease the server chose with at least the TTL
asked, as W0's `leaseStep .leaseGrant` commits it (the old lease table appended to `leaseHist`;
integration I1: the clause lacked it, so a real grant was not a `grantEff` step). -/
def grantEff (ttl : Int) (σ σ' : State) : Prop :=
  σ' = σ ∨ ∃ id ttl', σ.leases id = none ∧ ttl ≤ ttl' ∧
    σ' = { σ with leases := fun i => if i = id then some { ttl := ttl' } else σ.leases i,
                  granted := σ.granted ++ [id], leaseHist := σ.leaseHist ++ [σ.leases] }

/-- **The lease `id` revoked** (`Session.Close`): nothing, or its keys deleted at one revision and
the lease gone (the transition of a lease's expiry, `EnvStep.leaseExpire`). -/
def revokeEff (id : Int) (σ σ' : State) : Prop :=
  σ' = σ ∨ ∃ l, σ.leases id ≠ none ∧ σ.attachedKVs id l ∧ σ' = σ.revoke id l

/-- The permission's relation includes `E`. -/
def effIn (E T : State → State → Prop) : Prop := ∀ σ σ', E σ σ' → T σ σ'

/-! ## Options -/

section opts
variable [GooseExts]

/-- `sessionOptions`: the TTL, the lease to reuse (`0`: grant one) and the context (`none`: the
client's). -/
structure SessOpts where
  ttl : w64
  leaseID : w64
  ctx : Option GoInterface

/-- `NewSession`'s defaults: TTL `60`, no lease, the client's context. -/
def SessOpts.init : SessOpts := { ttl := W64 60, leaseID := W64 0, ctx := none }

/-- `WithTTL(ttl)`: kept if not positive (it logs a warning). -/
def withTTLM (ttl : w64) (o : SessOpts) : SessOpts :=
  if 0 < sint.Z ttl then { o with ttl := ttl } else o
def withLeaseM (id : w64) (o : SessOpts) : SessOpts := { o with leaseID := id }
def withContextM (ctx : GoInterface) (o : SessOpts) : SessOpts := { o with ctx := some ctx }

def applySessOptsM (gs : List (SessOpts → SessOpts)) (o : SessOpts) : SessOpts :=
  gs.foldl (fun o g => g o) o

/-- The isolation levels (`Isolation`). -/
def isoSS : w64 := W64 0
def isoS : w64 := W64 1
def isoRR : w64 := W64 2
def isoRC : w64 := W64 3

/-- The levels `mkSTM` supports (it panics on any other). -/
def isoValid (iso : w64) : Prop := iso = isoSS ∨ iso = isoS ∨ iso = isoRR ∨ iso = isoRC

/-- `stmOptions`: the level, the abort context (`none`: the client's), the keys to prefetch. -/
structure STMOpts where
  iso : w64
  ctx : Option GoInterface
  prefetch : List GoString

def STMOpts.init : STMOpts := { iso := isoSS, ctx := none, prefetch := [] }
def withIsolationM (iso : w64) (o : STMOpts) : STMOpts := { o with iso := iso }
def withAbortContextM (ctx : GoInterface) (o : STMOpts) : STMOpts := { o with ctx := some ctx }
def withPrefetchM (ks : List GoString) (o : STMOpts) : STMOpts :=
  { o with prefetch := o.prefetch ++ ks }

def applySTMOptsM (gs : List (STMOpts → STMOpts)) : STMOpts :=
  gs.foldl (fun o g => g o) STMOpts.init

end opts

/-! ## The STM's attempt -/

/-- One read of the attempt (a single-key get's response): its header's revision and the key's
key-value (`none`: absent). -/
structure ReadM where
  hdr : Nat
  kv : Option KV

/-- What a read returns (`respToValue`): the value, `""` if absent. -/
def ReadM.value (e : ReadM) : Bytes := (e.kv.map (·.value)).getD []
/-- The mod revision a read compares (`isKeyCurrent`), `0` if absent. -/
def ReadM.modRev (e : ReadM) : Nat := (e.kv.map (·.modRev)).getD 0

/-- One write of the attempt: a put (the request `OpPut(k, v, opts...)` builds), or a delete. -/
inductive WriteM where
  | put (p : PutReq)
  | del

/-- What `Get` returns for a written key: the value put, `""` for a delete. -/
def WriteM.value : WriteM → Bytes
  | .put p => p.value
  | .del => []

/-- The operation the commit sends for the write of `k`. -/
def WriteM.op (k : Key) : WriteM → RequestOp
  | .put p => .put p
  | .del => .deleteRange { key := k, rangeEnd := [], prevKv := false }

/-- **An attempt**: its reads (the read set) and writes (the write set), by key. -/
structure Attempt where
  reads : Key → Option ReadM
  writes : Key → Option WriteM

def Attempt.empty : Attempt := { reads := fun _ => none, writes := fun _ => none }

/-- Every read is the store `s`'s key-value of its key. -/
def Attempt.readsAgree (a : Attempt) (s : EtcdModel.Store) : Prop :=
  ∀ k e, a.reads k = some e → e.kv = (s k).map (KV.ofRec k)

/-- The read `e` of `k` is the key's key-value at some revision of `h` (at most its header's,
which `h` has reached). -/
def readOf (h : KVHist) (k : Key) (e : ReadM) : Prop :=
  e.hdr ≤ h.rev ∧ ∃ r, r ≤ e.hdr ∧ e.kv = ((h.storeAt r) k).map (KV.ofRec k)

/-- Every read is some revision's of `h` (`readOf`). -/
def Attempt.readsSeen (a : Attempt) (h : KVHist) : Prop :=
  ∀ k e, a.reads k = some e → readOf h k e

/-- **The attempt's writes applied at `σ`**, in one revision (the written keys in some order: the
write set is a map). -/
def Attempt.applied (a : Attempt) (σ σ' : State) : Prop :=
  ∃ ks : List Key, ks.Nodup ∧ (∀ k, k ∈ ks ↔ a.writes k ≠ none) ∧
    ∃ s' evs rs, TxnRun σ.kv σ.kv.store σ.leases (σ.kv.rev + 1)
        (ks.filterMap (fun k => (a.writes k).map (WriteM.op k))) (σ.kv.store, [])
        (.ok (s', evs, rs)) ∧
      σ' = σ.withKV (σ.kv.commit evs)

/-- **A committed attempt** at the level `iso`: `σ` to `σ'` is the attempt's writes applied, every
read is some revision's (`readsSeen`), and, but for `ReadCommitted`, every read is the key-value
at a revision `r` of `σ` (`r` is `σ`'s own revision unless the attempt is a `RepeatableReads` one
that wrote nothing); `SerializableSnapshot`: no written key was modified after any read's
header revision. -/
def stmCommitted (iso : w64) (a : Attempt) (σ σ' : State) : Prop :=
  a.applied σ σ' ∧ a.readsSeen σ.kv ∧
  (iso ≠ isoRC → ∃ r, r ≤ σ.kv.rev ∧
      ((iso ≠ isoRR ∨ ∃ k, a.writes k ≠ none) → r = σ.kv.rev) ∧ a.readsAgree (σ.kv.storeAt r)) ∧
  (iso = isoSS → ∀ k r, a.writes k ≠ none → σ.kv.store k = some r →
      ∀ k' e, a.reads k' = some e → r.modRev ≤ e.hdr)

/-- **What an STM may do** to the cluster's state at level `iso` for a closure whose successful
attempts satisfy `Rel`: nothing (reads, failed commits), or a committed attempt. -/
def stmEff (iso : w64) (Rel : Attempt → Prop) (σ σ' : State) : Prop :=
  σ' = σ ∨ ∃ a, Rel a ∧ stmCommitted iso a σ σ'

/-- **What `Get(ks...)` does** to the attempt (and returns): nothing and `""` for no key; the
value of the first written key of `ks`, the attempt unchanged; otherwise the value of a key of
`ks` as read, the reads extended by keys of `ks` only (with one key: that key's read; with
several, the code returns the first key found already read, counting the reads a failed commit
prefetched, which the attempt's model does not show). -/
def GetPost (ks : List Key) (a : Attempt) (v : Bytes) (a' : Attempt) : Prop :=
  a'.writes = a.writes ∧ (∀ k e, a.reads k = some e → a'.reads k = some e) ∧
  (∀ k, a'.reads k ≠ none → a.reads k ≠ none ∨ k ∈ ks) ∧
  (ks = [] → v = [] ∧ a' = a) ∧
  match ks.find? (fun k => decide (a.writes k ≠ none)) with
  | some k => a' = a ∧ v = ((a.writes k).map WriteM.value).getD []
  | none => ks ≠ [] → ∃ k ∈ ks, ∃ e, a'.reads k = some e ∧ v = e.value

/-- **What `Rev(k)` does**: `k` read (if not yet), its mod revision returned (`0` if absent). -/
def RevPost (k : Key) (a : Attempt) (rev : w64) (a' : Attempt) : Prop :=
  a'.writes = a.writes ∧ (∀ k' e, a.reads k' = some e → a'.reads k' = some e) ∧
  (∀ k', a'.reads k' ≠ none → a.reads k' ≠ none ∨ k' = k) ∧
  ∃ e, a'.reads k = some e ∧ rev = W64 e.modRev

/-! ### The STM's internals (pure) -/

/-- `isKeyCurrent(k, resp)`: `ModRevision(k) = ` the mod revision read (`0`: absent). -/
def curCmp (k : Key) (e : ReadM) : EtcdModel.Compare :=
  { result := cmpEqual, target := cmpTMod, key := k, rangeEnd := [],
    targetUnion := .modRevision e.modRev }

/-- `writeSet.cmps(rev)`'s comparison of `k`: `ModRevision(k) < rev`. -/
def writeCmp (rev : w64) (k : Key) : EtcdModel.Compare :=
  { result := cmpLess, target := cmpTMod, key := k, rangeEnd := [],
    targetUnion := .modRevision (sint.Z rev) }

/-- The reads `l` added (a later one of a key wins). -/
def addReads (rs : Key → Option ReadM) (l : List (Key × ReadM)) : Key → Option ReadM :=
  l.foldl (fun rs ke => fun k => if k = ke.1 then some ke.2 else rs k) rs

/-- The transaction reply `m` holds one single-key range reply per read of `es`, each with a header
of the read's revision. -/
def respReads (m : TxnRespM) (es : List ReadM) : Prop :=
  List.Forall₂ (fun r e => ∃ (mi : RangeRespM) (hm : HeaderM), r = .range mi ∧ mi.hdr = some hm ∧
    hm.revision = W64 e.hdr ∧ mi.kvs = (e.kv.map KeyValueM.ofKV).toList) m.responses es

/-- `ks` lists the keys of a map (`f k ≠ none`), each once (a `for range` over it). -/
def keysOf {V : Type} (f : Key → Option V) (ks : List Key) : Prop :=
  ks.Nodup ∧ ∀ k, k ∈ ks ↔ f k ≠ none

/-! ## The package's state -/

/-- `Mutex`'s fields `myKey`, `myRev`, `hdr`. -/
structure MutexSt where
  key : GoString
  rev : w64
  hdr : Loc

/-- `NewMutex`'s: no key, revision `-1`, no header. -/
def MutexSt.init : MutexSt := { key := [], rev := W64 (-1), hdr := null }
/-- After `Unlock` or a failed `TryLock`: key `"\x00"`, revision `-1`. -/
def MutexSt.released (st : MutexSt) : MutexSt := { st with key := [W8 0], rev := W64 (-1) }

/-- `Election`'s fields `leaderKey`, `leaderRev`, `leaderSession`, `hdr`. -/
structure ElectionSt where
  leaderKey : GoString
  leaderRev : w64
  leaderSession : Loc
  hdr : Loc

/-- The comparison `CreateRevision(k) = rev` (`IsOwner`, the election's fence). -/
def ownerCmp (k : GoString) (rev : w64) : EtcdModel.Compare :=
  { result := cmpEqual, target := cmpTCreate, key := k, rangeEnd := [],
    targetUnion := .createRevision (sint.Z rev) }

/-- The package's error variables. -/
inductive ConcErr where
  | locked | sessionExpired | lockReleased | electionNotLeader | electionNoLeader

section errs
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The global variable holding each error. -/
def ConcErr.global : ConcErr → GoString
  | .locked => go_etcd_io.etcd.client.v3.concurrency.ErrLocked
  | .sessionExpired => go_etcd_io.etcd.client.v3.concurrency.ErrSessionExpired
  | .lockReleased => go_etcd_io.etcd.client.v3.concurrency.ErrLockReleased
  | .electionNotLeader => go_etcd_io.etcd.client.v3.concurrency.ErrElectionNotLeader
  | .electionNoLeader => go_etcd_io.etcd.client.v3.concurrency.ErrElectionNoLeader

/-- What `init.spec` says of the error values `ev` (with `context.Canceled`'s value `cv` and `io.EOF`'s `eof`, the two
`*errorString`s W0's `callErr_errorsNew` admits): not
`nil`, pairwise distinct, none of etcd's errors (`errVal`: another type), each a fresh
`*errorString` (so neither `cv` nor `io.EOF`'s value `eof`). The values are not Lean constants: `errors.New` allocates them at
the package's initialization (verify-round A3 F4). -/
def concErrsOk (ev : ConcErr → GoInterface) (cv eof : GoInterface) : Prop :=
  (∀ e e', ev e = ev e' → e = e') ∧
  ∀ e, ev e ≠ GoInterface.nil ∧ ev e ≠ cv ∧ ev e ≠ eof ∧ (∀ x, ev e ≠ errVal x) ∧
    ∃ x : Loc, ev e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x

end errs

/-! ## Resources -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A permission lent for one call** (W0's `etcdPerm`, guarded by the caller's token `P`): the
reads' persistent permission (`etcdPeek`), and an update performing any transition `T σ σ'` that
can be fired only by whoever holds `P`, and gives `P` back at its commit. A call takes
`etcdLent γ T P ∗ P` and gives `P` back on its definite outcomes; on an outcome that may leave a
write pending (an indefinite error) `P` stays with that write. So while the caller holds `P`, the
package changes nothing: the caller can rely on its keys' contents and lease ids between calls.
`P := True` is the persistent permission of round 0. -/
def etcdLent (γ : Cluster) (T : State → State → Prop) (P : IProp GF) : IProp GF :=
  iprop(etcdPeek γ ∗ □ (P -∗ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
    <{ ∀∀ (σ' : State), ⌜T σ σ'⌝ ∗ etcdState γ σ', COMM P ∗ etcdLb γ σ ∗ etcdLb γ σ' }>))

/-- **The package's error variables hold `ev`**, read-only (persistent). A post returning the
error `e` says `globalAddr e.global ↦□ err`. -/
def concErrs (ev : ConcErr → GoInterface) : IProp GF :=
  iprop(□ ∀ e : ConcErr, globalAddr e.global ↦□ ev e)

/-- **`err` is none of the package's errors** (the values their variables hold). -/
def notConcErr (err : GoInterface) : IProp GF :=
  iprop(∃ ev : ConcErr → GoInterface, concErrs ev ∗ ⌜∀ e, err ≠ ev e⌝)

/-- **A session** `s` over the client `c` of `γ`, with the lease `id` (persistent). The principal
of its own requests (the grant, the keep-alive, `Close`'s revoke) is its options' context's, fixed
at `NewSession`; the mutexes and elections over it send theirs with each call's context. -/
opaque isSession [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (c : Loc) (γ : Cluster) (id : w64) : IProp GF := iprop(True)

/-- The `SessionOption` closure `f` acts as `g` (persistent). -/
opaque sessOptAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (f : GoFunc) (g : SessOpts → SessOpts) : IProp GF := iprop(True)
def sessOptsAt (sl : GoSlice) (gs : List (SessOpts → SessOpts)) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ [∗list] f; g ∈ fs; gs, sessOptAt f g)

/-- The `STMOption` closure `f` acts as `g` (persistent). -/
opaque stmOptAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (f : GoFunc) (g : STMOpts → STMOpts) : IProp GF := iprop(True)
def stmOptsAt (sl : GoSlice) (gs : List (STMOpts → STMOpts)) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ [∗list] f; g ∈ fs; gs, stmOptAt f g)

/-- **A mutex** `m` of the session `s` on the prefix `pfx` (its fields `s`, `pfx`; persistent). -/
opaque isMutex [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (m : Loc) (s : Loc) (pfx : GoString) : IProp GF := iprop(True)
/-- The mutex's other fields (exclusive). -/
opaque mutexSt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (m : Loc) (st : MutexSt) : IProp GF := iprop(True)

/-- **An election** `e` of the session `s` on the prefix `pfx` (its fields `session`, `keyPrefix`;
persistent). -/
opaque isElection [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (e : Loc) (s : Loc) (pfx : GoString) : IProp GF := iprop(True)
/-- The election's other fields (exclusive). -/
opaque electionSt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (e : Loc) (st : ElectionSt) : IProp GF := iprop(True)

/-- **The consumer of `Observe`'s channel** `ch` on the prefix `pfx` of the cluster `γ`, its values
read after the state `σ0` (exclusive). -/
opaque observeAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ch : GoChan) (γ : Cluster) (pfx : GoString) (σ0 : State) : IProp GF := iprop(True)

/-- **An STM** (the interface value `iv`, level `iso`) of the cluster `γ` as `who`, holding the
attempt `a` (exclusive). -/
opaque stmAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (iv : GoInterface) (γ : Cluster) (who : Principal) (iso : w64) (a : Attempt) :
  IProp GF := iprop(True)

/-- **An STM between attempts** (after `mkSTM` or a commit; `reset` starts the next attempt). -/
opaque stmStale [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (iv : GoInterface) (γ : Cluster) (who : Principal) (iso : w64) : IProp GF :=
  iprop(True)

/-- An option's context, if set, is a context (`ctxOk`) whose requests, from a client of default
principal `dflt`, are authenticated as `who` (W0's `ctxPrin dflt ctx who`); unset, the client's own
context is used, and its requests are the client's own principal's (`who = dflt`). -/
def optCtxOk (o : Option GoInterface) (dflt who : Principal) : IProp GF :=
  match o with
  | some ctx => iprop(Context.ctxOk ctx ∗ ctxPrin dflt ctx who)
  | none => iprop(⌜who = dflt⌝)

/-- A call's outcome that may be the STM's abort (`panic(stmError{err})`, `err ≠ nil`), which
`runSTM` recovers: a return `x` with `Q x`, or the abort with `A`. -/
def stmRet {V : Type} (r : val) (Q : V → IProp GF) (A : IProp GF) : IProp GF :=
  iprop((∃ x : V, ⌜r = #x⌝ ∗ Q x) ∨
    (⌜∃ err : GoInterface, err ≠ GoInterface.nil ∧
        r = PanicV #(interface.mkOk go_etcd_io.etcd.client.v3.concurrency.stmError.ty
          #(go_etcd_io.etcd.client.v3.concurrency.stmError.mk err))⌝ ∗ A))

/-- **The user's closure** `apply` (`func(STM) error`; persistent: run once per attempt): from any
attempt with no writes yet (a fresh one, or one with prefetched reads), on any STM, holding the caller's frame `F` (at some attempt), it returns an error, or
`nil` with an attempt satisfying `Rel`, `F` at the attempt it leaves; or it aborts through a
method's abort, `F` kept. It uses the STM only through `Get`, `Put`, `Rev`, `Del`. -/
def applyOk (apply : GoFunc) (γ : Cluster) (who : Principal) (F : Attempt → IProp GF)
    (Rel : Attempt → Prop) : IProp GF :=
  iprop(□ ∀ (iv : GoInterface) (iso : w64) (a : Attempt), ⌜∀ k, a.writes k = none⌝ →
    {{ stmAt iv γ who iso a ∗ ∃ b, F b }}
      (App (Val #apply) (Val #iv))
    {{ (r : val), RET r; stmRet r (fun err : GoInterface => iprop(∃ a',
        stmAt iv γ who iso a' ∗ F a' ∗ ⌜err = GoInterface.nil → Rel a'⌝)) (∃ b, F b) }})

/-- **What `NewSTM` returns** at the level `iso`, for a closure with frame `F` and relation `Rel`,
after the state `σ0` the caller knew, with the lent permission's token `P`: `nil`, a committed
attempt `a` (`Rel a`, `F a`) applied from `σ` (after `σ0`) to `σ'` (`stmCommitted`), the commit's
reply (succeeded), `P` back; or `nil` and an error, the frame given back (`P` not: a commit may be
pending). -/
def stmResult (γ : Cluster) (iso : w64) (F : Attempt → IProp GF) (Rel : Attempt → Prop)
    (P : IProp GF) (σ0 : State) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ (a : Attempt) (σ σ' : State) (m : TxnRespM),
      F a ∗ P ∗ etcdLb γ σ ∗ etcdLb γ σ' ∗ txnRespOwn resp (DFrac.own 1) m ∗
      ⌜Reach σ0 σ ∧ Rel a ∧ stmCommitted iso a σ σ' ∧ m.succeeded = true⌝) ∨
    (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ b, F b))

/-! ### Internal predicates (the package's own proofs) -/

/-- `observe`'s side of `Observe`'s channel, its values read after `σ0`. -/
opaque observeProd [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ch : GoChan) (γ : Cluster) (pfx : GoString) (σ0 : State) : IProp GF := iprop(True)
/-- The `stm` struct at `q` (a `*stm`, or a `*stmSerializable`'s embedded one) of `γ` as `who`,
at level `iso`, holding the attempt `a`, its gets' options `gs`. -/
opaque stmCoreAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (q : Loc) (γ : Cluster) (who : Principal) (iso : w64) (a : Attempt)
    (gs : List (OpM → OpM)) : IProp GF := iprop(True)
/-- The `stm` struct at `q` between attempts (its maps possibly `nil`). -/
opaque stmCoreStale [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (q : Loc) (γ : Cluster) (who : Principal) (iso : w64) (gs : List (OpM → OpM)) :
  IProp GF := iprop(True)
/-- A `*stmSerializable` at `p` holding the attempt `a` (its core, its prefetched reads). -/
opaque stmSerAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (γ : Cluster) (who : Principal) (iso : w64) (a : Attempt) : IProp GF :=
  iprop(True)
/-- A `*stmSerializable` at `p` between attempts. -/
opaque stmSerStale [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (γ : Cluster) (who : Principal) (iso : w64) : IProp GF := iprop(True)
/-- A `readSet` map holding the reads `rs` (each a response that is some revision's). -/
opaque readSetAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (m : GoMap) (γ : Cluster) (rs : Key → Option ReadM) : IProp GF := iprop(True)
/-- A `writeSet` map holding the writes `ws`. -/
opaque writeSetAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (m : GoMap) (ws : Key → Option WriteM) : IProp GF := iprop(True)

/-- A `*GetResponse` of a single-key get, read-only, modelled by the read `e`. -/
def readRespAt (p : Loc) (e : ReadM) : IProp GF :=
  iprop(∃ (m : RangeRespM) (hm : HeaderM), rangeRespOwn p DFrac.discard m ∗
    ⌜m.hdr = some hm ∧ hm.revision = W64 e.hdr ∧ m.kvs = (e.kv.map KeyValueM.ofKV).toList⌝)

/-! ## The STM's contracts -/

/-- **`Get(keys...)`** on the STM `iv`: the value (`GetPost`), or the abort. -/
def STM.GetTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (iso : w64) : Prop :=
  ∀ (a : Attempt) (sl : GoSlice) (ks : List Key),
  {{ stmAt (GF := GF) iv γ who iso a ∗ sl ↦*□ ks }}
    (App (Val f) (Val #sl))
  {{ (r : val), RET r; stmRet r (fun v : GoString => iprop(∃ a',
      stmAt iv γ who iso a' ∗ ⌜GetPost ks a v a'⌝)) iprop(True) }}

/-- **`Put(key, val, opts...)`**: the put `OpPut(key, val, opts...)` builds, in the write set
(`OpPut` must not panic: `putPanics`). The options are given back. -/
def STM.PutTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (iso : w64) : Prop :=
  ∀ (a : Attempt) (k v : GoString) (opts : GoSlice) (gs : List (OpM → OpM)),
  {{ stmAt (GF := GF) iv γ who iso a ∗ optsAt opts gs ∗ ⌜¬ (opPutM k v gs).putPanics⌝ }}
    (App (App (App (Val f) (Val #k)) (Val #v)) (Val #opts))
  {{ RET #(); optsAt opts gs ∗ stmAt iv γ who iso
      { a with writes := fun k' => if k' = k then some (.put (opPutM k v gs).putReq) else a.writes k' } }}

/-- **`Rev(key)`**: the key's mod revision as read (`RevPost`), or the abort. -/
def STM.RevTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (iso : w64) : Prop :=
  ∀ (a : Attempt) (k : GoString),
  {{ stmAt (GF := GF) iv γ who iso a }}
    (App (Val f) (Val #k))
  {{ (r : val), RET r; stmRet r (fun rev : w64 => iprop(∃ a',
      stmAt iv γ who iso a' ∗ ⌜RevPost k a rev a'⌝)) iprop(True) }}

/-- **`Del(key)`**: a delete of the key, in the write set. -/
def STM.DelTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (iso : w64) : Prop :=
  ∀ (a : Attempt) (k : GoString),
  {{ stmAt (GF := GF) iv γ who iso a }}
    (App (Val f) (Val #k))
  {{ RET #(); stmAt iv γ who iso
      { a with writes := fun k' => if k' = k then some .del else a.writes k' } }}

/-- **`commit()`** (the package's): the attempt's transaction; `nil` if a comparison failed (the
state unchanged), else the response of a committed attempt (`stmCommitted`); or the abort. The
STM is left between attempts (`stmStale`); the lent permission's token `P` back unless it aborts. -/
def STM.CommitTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (iso : w64) :
    Prop :=
  ∀ (a : Attempt) (T : State → State → Prop) (P : IProp GF) (σ0 : State),
  {{ stmAt (GF := GF) iv γ who iso a ∗ etcdLent γ T P ∗ P ∗ etcdLb γ σ0 ∗
      ⌜effIn (fun σ σ' => σ' = σ ∨ stmCommitted iso a σ σ') T⌝ }}
    (App (Val f) (Val #()))
  {{ (r : val), RET r; stmRet r (fun resp : Loc => iprop(stmStale iv γ who iso ∗ P ∗
      (⌜resp = null⌝ ∨ ∃ (σ σ' : State) (m : TxnRespM), etcdLb γ σ ∗ etcdLb γ σ' ∗
        ⌜Reach σ0 σ ∧ stmCommitted iso a σ σ' ∧ m.succeeded = true⌝ ∗
        txnRespOwn resp (DFrac.own 1) m))) iprop(True) }}

/-- **`reset()`** (the package's): a fresh attempt. -/
def STM.ResetTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (iso : w64) :
    Prop :=
  {{ stmStale (GF := GF) iv γ who iso }}
    (App (Val f) (Val #()))
  {{ RET #(); stmAt iv γ who iso Attempt.empty }}

/-! ## Laws -/

/-- **The fencing guarantee** (pure): after a state `σ` where no key under `pfx` is older than a
revision `c` it has reached, any later state where `k` (under `pfx`) has create revision `c` is
one where `k` is the oldest key under `pfx`. (Keys created after `σ` are younger than `c`; a key
older than `c` present later was present at `σ`, its create revision unchanged.) -/
def fence.spec : Prop := ∀ (pfx k : GoString) (c : Nat) (σ σ' : State),
  noOlder pfx c σ.kv.store → c ≤ σ.kv.rev → Reach σ σ' → pfx <+: k →
  (∃ r, σ'.kv.store k = some r ∧ r.createRev = c) → holdsAt pfx k c σ'.kv.store

/-- **The package's error variables** hold some values `ev`, read-only, with `concErrsOk` against
`context.Canceled`'s and `io.EOF`'s values (verify-round A3 F4: `errors.New`'s fresh allocations, compared while
still owned; the context package is initialized first). With W0's `callErr_errorsNew`, no client
call's error is one of them. -/
def init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ⊢
    ∃ (ev : ConcErr → GoInterface) (cv eof : GoInterface),
      concErrs (GF := GF) ev ∗ globalAddr context.Canceled ↦□ cv ∗ globalAddr io.EOF ↦□ eof ∗
      ⌜concErrsOk ev cv eof⌝

def handles_persistent.spec : Prop :=
  (∀ s c γ id, Persistent (isSession (GF := GF) s c γ id)) ∧
  (∀ f g, Persistent (sessOptAt (GF := GF) f g)) ∧
  (∀ f g, Persistent (stmOptAt (GF := GF) f g)) ∧
  (∀ m s pfx, Persistent (isMutex (GF := GF) m s pfx)) ∧
  (∀ e s pfx, Persistent (isElection (GF := GF) e s pfx))

/-- A session's client and lease: its fields, read-only. -/
def isSession_client.spec : Prop := ∀ s c γ id,
  isSession (GF := GF) s c γ id ⊢
    ⌜s ≠ null⌝ ∗ s.[go_etcd_io.etcd.client.v3.concurrency.Session, go!"client"] ↦□ c ∗
      s.[go_etcd_io.etcd.client.v3.concurrency.Session, go!"id"] ↦□ id

/-- Running a `SessionOption`: on the options at `p` (modelled by `o`, the context aside: its
field holds `ctx`), with a logger, they become `g o`. -/
def sessOptAt_call.spec : Prop := ∀ (f : GoFunc) (g : SessOpts → SessOpts) (p : Loc)
    (ov : go_etcd_io.etcd.client.v3.concurrency.sessionOptions) (lg : Loc),
  {{ sessOptAt (GF := GF) f g ∗ p ↦ ov ∗ Zap.isLogger lg }}
    (App (App (Val #f) (Val #p)) (Val #lg))
  {{ RET #(); ∃ ov' : go_etcd_io.etcd.client.v3.concurrency.sessionOptions, p ↦ ov' ∗
      ⌜let o' := g { ttl := ov.ttl', leaseID := ov.leaseID', ctx := none }
       ov'.ttl' = o'.ttl ∧ ov'.leaseID' = o'.leaseID ∧
       ov'.ctx' = o'.ctx.getD ov.ctx'⌝ }}

/-- Running an `STMOption` on the options at `p`. -/
def stmOptAt_call.spec : Prop := ∀ (f : GoFunc) (g : STMOpts → STMOpts) (p : Loc)
    (ov : go_etcd_io.etcd.client.v3.concurrency.stmOptions) (pf : List GoString),
  {{ stmOptAt (GF := GF) f g ∗ p ↦ ov ∗ ov.prefetch' ↦*□ pf }}
    (App (Val #f) (Val #p))
  {{ RET #(); ∃ ov' : go_etcd_io.etcd.client.v3.concurrency.stmOptions, p ↦ ov' ∗
      ⌜let o' := g { iso := ov.iso', ctx := none, prefetch := pf }
       ov'.iso' = o'.iso ∧ ov'.ctx' = o'.ctx.getD ov.ctx'⌝ ∗
      ov'.prefetch' ↦*□ (g { iso := ov.iso', ctx := none, prefetch := pf }).prefetch }}

/-- An election's leader session is `nil` or its own session. -/
def electionSt_session.spec : Prop := ∀ e s pfx st,
  isElection (GF := GF) e s pfx ∗ electionSt e st ⊢
    ⌜st.leaderSession = null ∨ st.leaderSession = s⌝

/-- **Receiving from `Observe`'s channel**: closed (nothing more), or a `*GetResponse` with one
key-value `v`, read-only, its header a revision of a state `σ` reached after `σ0`; under the
compaction condition (W0's `exactFrom` from just after `σ0`: the watch's events are exact only
under it, 1b's `watchStep`), the header's revision is at least `v`'s mod revision and `v` was the
prefix's oldest key's write at a revision of `σ` (`ObservedAt`). (No order between headers: after a
reconnect, a lagging member's header may be lower: 1b's review.) -/
def observeAt_recv.spec : Prop := ∀ (ch : GoChan) (γ : Cluster) (pfx : GoString) (σ0 : State),
  {{ observeAt (GF := GF) ch γ pfx σ0 }}
    (App (Val (chan.receive (go.GoType.PointerType go_etcd_io.etcd.client.v3.GetResponse.ty)))
      (Val #ch))
  {{ (p : Loc) (ok : Bool), RET (PairV #p #ok);
      if ok then ∃ (m : RangeRespM) (hm : HeaderM) (v : KV) (σ : State),
        rangeRespOwn p DFrac.discard m ∗ etcdLb γ σ ∗
        ⌜m.hdr = some hm ∧ m.kvs = [KeyValueM.ofKV v] ∧ Reach σ0 σ ∧
          sint.Z hm.revision ≤ σ.kv.rev ∧
          (EtcdModel.exactFrom σ.kv (σ0.kv.rev + 1) →
            (v.modRev : Int) ≤ sint.Z hm.revision ∧ ObservedAt pfx v σ.kv)⌝ ∗
        observeAt ch γ pfx σ0
      else ⌜p = null⌝ }}

/-- **Receiving from `Observe`'s channel in a `select`** (v3election's handler): the channel's
receive update (Perennial's `recvAu`), with `observeAt_recv`'s outcomes. -/
def observeAt_recvAu.spec : Prop := ∀ (ch : GoChan) (γ : Cluster) (pfx : GoString) (σ0 : State)
    (Φ : Loc → Bool → IProp GF),
  observeAt (GF := GF) ch γ pfx σ0 ⊢
    ∃ γc : ChanNames, isChan ch γc Loc ∗
      (£ 1 ∗ £ 1 -∗
        (▷ ∀ (p : Loc) (ok : Bool), (if ok then ∃ (m : RangeRespM) (hm : HeaderM) (v : KV) (σ : State),
            rangeRespOwn p DFrac.discard m ∗ etcdLb γ σ ∗
            ⌜m.hdr = some hm ∧ m.kvs = [KeyValueM.ofKV v] ∧ Reach σ0 σ ∧
              sint.Z hm.revision ≤ σ.kv.rev ∧
              (EtcdModel.exactFrom σ.kv (σ0.kv.rev + 1) →
                (v.modRev : Int) ≤ sint.Z hm.revision ∧ ObservedAt pfx v σ.kv)⌝ ∗
            observeAt ch γ pfx σ0
          else ⌜p = null⌝) -∗ Φ p ok) -∗
        recvAu γc Loc Φ)

/-- The STM's methods: the user's view (`Get`, `Put`, `Rev`, `Del`) and the package's (`commit`,
`reset`), on the interface value. -/
def stmAt_methods.spec : Prop := ∀ (iv : GoInterface) (γ : Cluster) (who : Principal) (iso : w64),
  STM.GetTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.concurrency.STM.ty @!! go!"Get") iv γ who iso ∧
  STM.PutTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.concurrency.STM.ty @!! go!"Put") iv γ who iso ∧
  STM.RevTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.concurrency.STM.ty @!! go!"Rev") iv γ who iso ∧
  STM.DelTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.concurrency.STM.ty @!! go!"Del") iv γ who iso ∧
  STM.CommitTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.concurrency.STM.ty @!! go!"commit") iv γ who iso ∧
  STM.ResetTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.concurrency.STM.ty @!! go!"reset") iv γ who iso

/-- **The attempt's reads are the cluster's** (each some revision's of a reached state), for the
closure to use during the attempt. -/
def stmAt_reads.spec : Prop := ∀ (iv : GoInterface) (γ : Cluster) (who : Principal) (iso : w64)
    (a : Attempt),
  stmAt (GF := GF) iv γ who iso a ⊢ stmAt iv γ who iso a ∗ ∃ σ : State, etcdLb γ σ ∗ ⌜a.readsSeen σ.kv⌝

def applyOk_persistent.spec : Prop := ∀ apply γ who F Rel,
  Persistent (applyOk (GF := GF) apply γ who F Rel)

end res

end Concurrency
end EtcdGrove
end Perennial
