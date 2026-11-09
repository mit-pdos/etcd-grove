/-
# `server/lease`: the lessor (batch 3c): the vocabulary

etcd's lessor (`lessor.go`, `lease.go`) keeps a member's leases: the live leases with their granted
TTLs (`leaseMap`), the keys attached to each (`itemSet` of each `*Lease`, and the reverse map
`itemMap`), the lease bucket of the backend it persists them to, and, on the leader (the *primary*
lessor), their expiries in wall-clock time. Its users:

* the **apply thread** (3a's applier, 3b's txn, 3e's mvcc, 2d's `applySnapshot`), the only writer:
  `Grant`, `Revoke`, `Checkpoint` (applier), `Lookup` (the put's and the auth applier's lease
  check), `GetLease`/`Attach`/`Detach` (mvcc's put and delete; `Restore`'s re-attachment),
  `SetRangeDeleter` (mvcc's `NewStore`, `newWatchableStore`), `Recover` (`applySnapshot`), `Promote`
  (`applyEntryNormal`'s empty entry on the leader);
* the **request path** (2c), any goroutine: `Lookup`, `Leases`, `Renew`, and the `*Lease`'s `Keys`,
  `TTL`, `Remaining`, `Demoted`, `ID`;
* the **server's lifecycle** (2d, 2e): `NewLessor`, `SetCheckpointer`, `ExpiredLeasesC` (`run`'s
  expiry arm), `Demote` (the ready handler's leadership change), `Stop` (`Cleanup`).

Snippets: `examples/specreq/lease/` (`lessor.go`: grant, attach and lookup; revoke through the
range deleter; the lease list; recover; renew and the primary; the expiry channel; stop).

## The model (transparent)

* `Cfg`: what the specs need of the lessor's configuration: its minimum TTL (`MinLeaseTTL`, every
  grant and every recovered lease raised to it) and the **expiry mode** chosen at `NewLessor`
  (`true`: the expiry channel may deliver any live lease at any time; `false`: under the trusted
  deployment premise `leasesOutliveRun`, it never delivers).
* `LessorState`: **the lessor's state as its writer sees it**: `leases` (the live leases: id to the
  `*Lease` object and its granted TTL), `items` (`itemMap`: a key's lease, `0` for none), `keys` (the
  item set of every `*Lease` object, live or not: a reader holding a revoked lease's object still
  calls `Keys()` on it), `bkt` (the backend's lease bucket, id to TTL, which may differ from the live
  TTL: a recovered lease is raised to the minimum in memory only), `be` (the backend it writes),
  `rd` (the range deleter). **Not modelled**: time (expiries, the remaining TTL, its checkpoints:
  `Checkpoint` changes at most the bucket's TTL of a recovered lease, `Remaining()` returns any
  duration), and whether the lessor is primary (`Promote`/`Demote` change nothing here; `Renew` may
  answer `ErrNotPrimary` at any time). `items` and `keys` are two maps, as in Go: the lessor does
  not keep them in agreement (`Attach` of a key attached elsewhere overwrites `itemMap` only);
  mvcc's callers keep them so (`req/go_etcd_io_etcd_server_v3_storage_mvcc.md`, "from 3c").
* The transitions (`grant`, `attach`, `detach`, `persist`, `remove`, `loaded`) are the code's, one
  per atomic step under `le.mu`.

## Resources

* `isLessor le γ c` (persistent): `le` is a `*lessor` with names `γ` and configuration `c`: its
  mutex and the invariant it protects, its logger (`Zap.isLogger`: zap's zero logger panics,
  `specs-ref`'s axiom sweep B3-2), its cluster (`clusterOk`), its expiry channel's protocol, its run
  loop.
* `lessorState γ n ls` (exclusive, timeless): **the writer's token: the lessor's state is `ls`, the
  `n`-th of its history**. Every method that changes the state takes it (the apply thread holds it;
  mvcc's writes and the range deleter borrow it from there). The lease bucket of `ls.be` is inside it
  (`lessorState_bkt` lends it out), so is the lessor's open share of that backend (`beOk ls.be`,
  `lessorState_beOk` lends it out: the server's shutdown takes it back before the backend's
  `Close`), and one reader token (`lessorState_reader`).
* `lessorAt γ n ls` (persistent, timeless): **the lessor's `n`-th state was `ls`** (its history: every
  state a writer's step produced). Readers (`Lookup`, `Leases`, `GetLease`, `Keys`, `Renew`) take
  `lessorLb γ i` (a lower bound) and answer from a state `j ≥ i` of the history, which they return
  (`lessorAt γ j ls'`): a writer, holding `lessorState γ n ls` and passing `lessorAt γ n ls`, gets
  `j = n` (`lessorState_le`, `lessorAt_agree`), so one spec serves both. The server (2d) ties the
  history to its own (`histAt`): which lessor state each applied entry ends at.
* `lessorReaders γ n` (exclusive, counted, splits): **`n` reader tokens**, each a reader slot of the
  lessor's `RWMutex`es (`le.mu`, each object's `mu` and `expiryMu`): every method that read-locks one
  takes a token and gives it back (the bounds plan: the count is the lessor's, `lessorTokN`, given by
  `NewLessor`; the user's decision of 2026-11-07 for mvcc's readers, applied here). The writer
  borrows one from its token.
* `leaseObj γ l id ttl` (persistent): `l` is a `*Lease` object of this lessor, of lease `id` and
  granted TTL `ttl` (its `ID` and `ttl` fields never change after it is published).
* `lessorStop le` (exclusive): the right to `Stop()` (a second `Stop` closes `stopC` twice).
* `lessorCkptTok le` (exclusive): the right to `SetCheckpointer` once (`NewLessor`'s; Go reads
  `le.cp` unlocked after a locked test, so a second call races:
  `nonissues/etcd-lease-setcheckpointer-once.md`). `SetCheckpointer` turns it into `ckptGate le R`
  (persistent): the checkpointer is callable once `R` holds; `lessorCkptTok_gate` gives `ckptGate le
  True` for a lessor that never gets a checkpointer. `Promote` takes `ckptGate le R ∗ □ R`: the
  lessor calls the checkpointer only when primary, so only after a `Promote` (the server's closure
  needs the server started: `R := srvStarted`).
* `expiredCh γ c ch` (persistent): `ch` is the lessor's expiry channel; `expiredCh_recv` is its
  receive.
* `rdOk`, `ckptOk` (transparent): the contracts of the two callbacks the lessor calls (the range
  deleter for `Revoke`, the checkpointer for `Renew` and the run loop).
* Provisional, other batches' (still provisional after the integration, I5: their owners have no
  such predicate yet): `beOk be`, `beLeases be B`, `beHook be Pk f`, `beTxHeld be` (4a/4b,
  `req/go_etcd_io_etcd_server_v3_storage_backend.md` and `..._schema.md`, "from 3c"; the hook's
  contract is mvcc's `Mvcc.hookRun`, as mvcc's write path takes it); `clusterOk cl` (2e's
  membership, `RaftCluster.Version`: no spec of it in `membership/` yet). Their intended
  realizations over the owners' current vocabulary are in their docstrings: 4b's lease functions
  (`Schema.MustUnsafePutLease`, `MustUnsafeGetAllLeases`, `UnsafeDeleteLease`,
  `UnsafeCreateLeaseBucket`) are over `Schema.txWr`/`txRd tx S R` and the bucket's encoding
  `Schema.leaseBktIs`; 4a's backend over `Backend.isBackend`, `Backend.beHook`, `Backend.beSess`;
  mvcc identifies `beTxHeld` with its `Mvcc.kbHeld` (`Mvcc.mvccDeleter_rdOk`'s premise).
* `leasesOutliveRun` (opaque `Prop`): **the trusted deployment premise about time** (W0's
  `EnvCfg.leaseExpiry = false`, `top.md` K2): no run loop of this run's lessors finds a lease
  expired. Taken by `NewLessor` for the expiry mode `false`; nothing proves it.

## Intended realization

`isLessor le γ c`: `le`'s read-only fields (`lg` with `isLogger`, `cluster` with `clusterOk`,
`minLeaseTTL = c.minTTL`, `checkpointInterval`, `expiredC`, `stopC`, `doneC`, `leaseRevokeRate`
non-negative), and `le.mu`'s invariant: the authority of a ghost variable `γ.cur` (`lessorState`'s
other half: the current `n`, `ls`) and of a `mono_list` `γ.hist` of the states (`lessorAt` its
fragments), with the Go maps at `ls` (`leaseMap` the live objects, `itemMap` at `ls.items`),
`le.b = ls.be`, `le.rd = ls.rd` (a half: the writer's token holds the other, since `Revoke` reads it
unlocked), the checkpoint heap well-formed (`queueAt`), `demotec` with its close right, each live
object's `revokec` close right, and `le.cp`: `nil` with `lessorCkptTok`'s other half, or, once set,
frozen (`↦□`) with `ckptOk cp R` and the gate, and `□ R` while `demotec` is not `nil` (deposited by
`Promote`). **The notifier** is owned by the write-lock holder or by the run loop's reader section
(`revokeExpiredLeases` changes it under `RLock`, and is the only reader that touches it): `le.mu`'s
invariant holds it with a run-loop token, which the run loop's read section takes and every writer
section takes too. **The lease bucket** `beLeases ls.be ls.bkt` is in the writer's token, not in the
lock (only the token's holder writes it: `Grant`, `Checkpoint`, `Revoke`, `Recover`); so are the open
share `beOk ls.be` (only the token's holder calls the backend: `persistTo`'s lock, `initAndRecover`'s
lock and `ForceCommit`) and one of the reader tokens. Each `*Lease`'s `mu` invariant holds its `itemSet` at `ls.keys l` for the current state
(by a ghost map `γ.keys`, object to set, its authority in an invariant opened by holders of `le.mu`
and `l.mu` together: `Keys()` reads under `l.mu` alone); `leaseObj γ l id ttl`: `l.ID ↦□ id`,
`l.ttl ↦□ ttl`, the locks' invariants. `lessorReaders γ n`: `n` reader slots of each `RWMutex`.
The run loop: holds `isLessor` and its own reader token; it sends live objects on `expiredC` only
with `c.expiry = true` (with `false`, an expiry found would contradict `leasesOutliveRun`: the run
loop's time reasoning is the trusted part, `runLoop` being untranslated).

## Laws

`persistent`, `timeless`, `exclusive`; `isLessor_ne_null`, `isLessor_agree`; `lessorState_at`, `lessorAt_agree`, `lessorState_le`,
`lessorAt_obj`, `lessorAt_minTTL`, `leaseObj_id`, `leaseObj_live`, `leaseObj_agree`,
`lessorState_bkt`, `lessorState_beOk`, `lessorState_reader`, `lessorReaders_split`, `lessorCkptTok_gate`,
`expiredCh_recv`, `init`.
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.lease
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.lease
public import Spec.go_etcd_io.etcd.api.v3.Model
public import Spec.go_uber_org.zap.Api
public import Spec.context.Api
public import Spec.google_golang_org.protobuf.proto.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiStorage

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Lease

open Iris Iris.BI EtcdModel

/-- The lessor's ghost names: opaque. -/
opaque Names : Type := Unit

/-! ## The model -/

/-- What the specs need of a lessor's configuration: the minimum TTL (`LessorConfig.MinLeaseTTL`)
and the expiry mode chosen at `NewLessor` (see the header). -/
structure Cfg where
  minTTL : Int
  expiry : Bool

/-- The TTL a lease asked with `ttl` is granted (or recovered with): raised to the minimum. -/
def grantTTL (c : Cfg) (ttl : Int) : Int := max ttl c.minTTL

/-- A live lease: its `*Lease` object and granted TTL. -/
structure LeaseEnt where
  obj : Loc
  ttl : Int

section model
variable [GooseExts]

/-- **The lessor's state** (see the header). -/
structure LessorState where
  /-- `leaseMap`: the live leases -/
  leases : Int → Option LeaseEnt
  /-- `itemMap`: each key's lease (`0`: none) -/
  items : Key → Int
  /-- the item set of each `*Lease` object (live or not) -/
  keys : Loc → Key → Prop
  /-- the backend's lease bucket: id to the TTL stored -/
  bkt : Int → Option Int
  /-- the backend the lessor persists to (`le.b`) -/
  be : GoInterface
  /-- the range deleter (`le.rd`; `func.nil` until set) -/
  rd : GoFunc

/-- The live leases as W0's lease table (id to granted TTL). -/
def LessorState.table (ls : LessorState) : Int → Option LeaseRec :=
  fun id => (ls.leases id).map (fun e => { ttl := e.ttl })

/-- `Grant`'s step: lease `id` live with the fresh object `l` (its item set empty) and TTL `ttl`,
in memory and in the bucket. -/
def LessorState.grant (ls : LessorState) (id : Int) (l : Loc) (ttl : Int) : LessorState :=
  { ls with leases := fun i => if i = id then some { obj := l, ttl := ttl } else ls.leases i,
            keys := fun o => if o = l then (fun _ => False) else ls.keys o,
            bkt := fun i => if i = id then some ttl else ls.bkt i }

/-- `Attach(id, ks)`'s step (lease `id` live): each key's `itemMap` entry set to `id`, and the keys
added to the lease's item set. Nothing for a lease not live (`ErrLeaseNotFound`). -/
def LessorState.attach (ls : LessorState) (id : Int) (ks : List Key) : LessorState :=
  match ls.leases id with
  | none => ls
  | some e => { ls with items := fun k => if k ∈ ks then id else ls.items k,
                        keys := fun o k => ls.keys o k ∨ (o = e.obj ∧ k ∈ ks) }

/-- `Detach(id, ks)`'s step (lease `id` live): each key's `itemMap` entry deleted (whatever lease it
named), and the keys removed from the lease's item set. Nothing for a lease not live. -/
def LessorState.detach (ls : LessorState) (id : Int) (ks : List Key) : LessorState :=
  match ls.leases id with
  | none => ls
  | some e => { ls with items := fun k => if k ∈ ks then 0 else ls.items k,
                        keys := fun o k => ls.keys o k ∧ ¬ (o = e.obj ∧ k ∈ ks) }

/-- `Checkpoint`'s step when it persists (`shouldPersistCheckpoints()`, lease `id` live): the
lease's record rewritten with its live TTL (a recovered lease's TTL raised in memory reaches the
bucket). -/
def LessorState.persist (ls : LessorState) (id : Int) : LessorState :=
  match ls.leases id with
  | none => ls
  | some e => { ls with bkt := fun i => if i = id then some e.ttl else ls.bkt i }

/-- `Revoke`'s last step: lease `id` gone from memory and from the bucket (its object's item set
kept: a reader may still hold the object). -/
def LessorState.remove (ls : LessorState) (id : Int) : LessorState :=
  { ls with leases := fun i => if i = id then none else ls.leases i,
            bkt := fun i => if i = id then none else ls.bkt i }

/-- The state `NewLessor` and `Recover` load (`initAndRecover`): the leases of the bucket `B` of
backend `be`, each with a fresh object `objs id` (its item set empty) and its TTL raised to the
minimum; no item attached; the other objects' item sets `old` kept. -/
def LessorState.loaded (c : Cfg) (be : GoInterface) (rd : GoFunc) (B : Int → Option Int)
    (objs : Int → Loc) (old : Loc → Key → Prop) : LessorState :=
  { leases := fun i => (B i).map (fun t => { obj := objs i, ttl := grantTTL c t }),
    items := fun _ => 0,
    keys := fun o k => (¬ ∃ i, B i ≠ none ∧ objs i = o) ∧ old o k,
    bkt := B, be := be, rd := rd }

end model

/-- **Trusted deployment premise about time** (W0's `EnvCfg.leaseExpiry = false`, `top.md` K2): no
run loop of this run's lessors finds a lease expired (`Remaining() ≤ 0` of a lease in its notifier
while primary: the expiry `refresh` set from the checkpointed remaining TTL, or the TTL, plus
`Promote`'s extension, has not passed). Opaque: nothing proves it; the program that starts the
cluster takes it. -/
opaque leasesOutliveRun : Prop

/-! ## Resources -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`le` is a lessor** with names `γ` and configuration `c` (persistent; see the header). -/
opaque isLessor (le : Loc) (γ : Names) (c : Cfg) : IProp GF := iprop(True)

/-- **The writer's token: the lessor's state is `ls`, the `n`-th of its history** (exclusive). -/
opaque lessorState (γ : Names) (n : Nat) (ls : LessorState) : IProp GF := iprop(True)

/-- **The lessor's `n`-th state was `ls`** (persistent). -/
opaque lessorAt (γ : Names) (n : Nat) (ls : LessorState) : IProp GF := iprop(True)

/-- The lessor's history has an `n`-th state (a reader's lower bound). -/
def lessorLb (γ : Names) (n : Nat) : IProp GF := iprop(∃ ls, lessorAt γ n ls)

/-- **`l` is a `*Lease` object of this lessor**, of lease `id` and granted TTL `ttl` (persistent). -/
opaque leaseObj (γ : Names) (l : Loc) (id : Int) (ttl : Int) : IProp GF := iprop(True)

/-- The right to `Stop()` the lessor (exclusive). -/
opaque lessorStop (le : Loc) : IProp GF := iprop(True)

/-- **The number of reader tokens a new lessor gives** (sealed). -/
opaque lessorTokN : Nat

/-- **`n` reader tokens** of the lessor `γ` (exclusive, counted): reader slots of its `RWMutex`es. -/
opaque lessorReaders (γ : Names) (n : Nat) : IProp GF := iprop(True)

/-- The right to `SetCheckpointer` once (exclusive). -/
opaque lessorCkptTok (le : Loc) : IProp GF := iprop(True)

/-- **The lessor's checkpointer is callable once `R` holds** (persistent; `SetCheckpointer`'s, or
`lessorCkptTok_gate`'s with `R = True`). -/
opaque ckptGate (le : Loc) (R : IProp GF) : IProp GF := iprop(True)

/-- `ch` is the expiry channel (`ExpiredLeasesC()`) of the lessor `γ` configured `c` (persistent). -/
opaque expiredCh (γ : Names) (c : Cfg) (ch : GoChan) : IProp GF := iprop(True)

/-- `le` as a `Lessor` interface value. -/
def lessorIface (le : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty) #le

/-- The lessor's error `g` (`ErrNotPrimary`, `ErrLeaseNotFound`, ...) is the value `e`. -/
def errIs (g : GoString) (e : GoInterface) : IProp GF := iprop(globalAddr g ↦□ e)

/-! ### Provisional: other batches' vocabulary -/

/-- (provisional, 4a's) **An open share of the backend `be`**: its batch transaction may be fetched
(`BatchTx()`), locked outside an apply (`LockOutsideApply`, no hook) or inside one (with `beHook`),
unlocked, and force-committed (`ForceCommit()`). **Not persistent** (integration I5, 4a's request,
`req/..._lease.md`, "from 4a"): after the backend's `Close` these panic or are fatal, so the share
is held (in the writer's token, `lessorState_beOk`) and handed back before the close. Intended
realization (4a's current API): `∃ γb b p Pk q, ⌜be = Backend.beIface b⌝ ∗ Backend.isBackend γb b p
Pk ∗ Backend.beOpen γb q` (the lease bucket written under the lock's session, `Backend.beSess`, as
`Schema.txWr`; `ForceCommit`'s commit request `Backend.beReq` is still to be matched: 4a is
repairing). -/
opaque beOk (be : GoInterface) : IProp GF := iprop(True)

/-- (provisional, 4b's over 4a's) **The lease bucket of `be`, as its batch transaction holds it (the
last commit with the pending writes), decodes to `B`** (id to stored TTL; each record a
`leasepb.Lease` that unmarshals, so `MustUnsafeGetAllLeases` does not panic; its `RemainingTTL` not
modelled). Exclusive: its holder is the bucket's only writer (`MustUnsafePutLease`,
`UnsafeDeleteLease` move it, under the batch transaction's lock). Intended realization (4b's
answer, `req/..._lease.md`, "from 4b"): the caller's share `R V` of 4a's batch view, with `V .lease
= some m ∧ Schema.leaseBktIs m L ∧ ∀ i, B i = (L (W64 i)).map (fun r => sint.Z r.2.1)` (the records
keyed by the id's bytes; the remaining TTL dropped), the scope `S` with `lease` whole, for the
`Schema.txRd`/`txWr` bundles of `be.BatchTx()` that 4a gives the lock's holder. -/
opaque beLeases (be : GoInterface) (B : Int → Option Int) : IProp GF := iprop(True)

/-- (provisional, 4a's) **`be`'s batch lock has the invariant `Pk` and its post-lock hook is `f`**
(`nil`: none), for good (persistent): `LockInsideApply` gives `Pk` and runs `f` (`Mvcc.hookRun Pk f
Pre Q`: the caller's `Pre` to `Q`), `Unlock` takes `Pk` back. mvcc's `mvccBackend`/`hookIs` say the
same of its storage; 4a identifies them. Intended realization (4a's current API): `∃ γb b p, ⌜be =
Backend.beIface b⌝ ∗ Backend.isBackend γb b p Pk ∗ Backend.beHook γb DFrac.discard f` (4a's
`keyBackend_intro` identifies `Mvcc.storageHook B dq f` with `Backend.beHook γb dq f` the same
way). -/
opaque beHook (be : GoInterface) (Pk : IProp GF) (f : GoFunc) : IProp GF := iprop(True)

/-- (provisional, 4a's) **This thread holds `be`'s batch transaction lock** (an mvcc write
transaction is open: `Write()` locked it, `End()` unlocks it), so it may make unsafe writes.
Exclusive. mvcc's `Mvcc.kbHeld B` for `be = GoInterface.ok (Mvcc.storageVal B)` (the identification
is `Mvcc.mvccDeleter_rdOk.spec`'s premise `□ (kbHeld B ∗-∗ beTxHeld _)`; 4a's `keyBackend_intro`
realizes `kbHeld` as the lent session, `Backend.beSess`). -/
opaque beTxHeld (be : GoInterface) : IProp GF := iprop(True)

/-- (provisional, 2e's membership) **`cl` is a lessor's `cluster`**: `Version()` may be called from
any goroutine and returns `nil` or a readable `*semver.Version`. Persistent. Intended discharge: a
law of 2e's `Membership.isCluster c γ cid lid ⊢ clusterOk (iface c)` with a spec of
`RaftCluster.Version` (neither exists yet: `req/..._membership.md`, "from 3c"). -/
opaque clusterOk (cl : GoInterface) : IProp GF := iprop(True)

/-! ### The callbacks' contracts -/

/-- **The checkpointer's contract** (persistent), gated on `R`: once `R` holds, `cp(ctx, lc)` for
any context and an owned `*LeaseCheckpointRequest` returns `nil` or `ErrNotPrimary` (the server's
closure needs the server started, `R := srvStarted`: before `start` it panics; the lessor calls it
only when primary, after a `Promote` that brought `□ R`). The lessor calls it with
`context.Background()` from `Renew` (which returns its error) and the run loop (which ignores it).
The server's closure (`NewServer`, `server.go:395`: `ErrNotPrimary` unless `ensureLeadership()`,
else `raftRequest` of the checkpoint, a no-op of W0's model, its error dropped, and `nil`) meets it.
The error set is restricted so that `Renew`'s errors are the lessor's own (2c's need). -/
def ckptOk (cp : GoFunc) (R : IProp GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterface) (lc : Loc) (m : Proto.Content),
    {{ R ∗ Context.ctxOk ctx ∗
        Proto.msgAt go_etcd_io.etcd.api.v3.etcdserverpb.LeaseCheckpointRequest.ty lc (DFrac.own 1) m }}
      (App (App (Val #cp) (Val #ctx)) (Val #lc))
    {{ (err : GoInterface), RET #err;
        ⌜err = interface.nil⌝ ∨ errIs go_etcd_io.etcd.server.v3.lease.ErrNotPrimary err }})

/-- **A range deleter's contract for one revocation** (transparent), from the writer's state `n`,
`ls` at the call: the caller's resource `P` lets `rd()` open a deletion transaction `td`, whose
client-side state `D td ks n' ls'` records the keys deleted so far and the lessor's state after
them; each `td.DeleteRange(k, nil)` borrows the lessor's writer token (mvcc's delete detaches the
key: its `GetLease`, `Detach`) and gives it back at a later state with the same live leases, bucket,
backend and deleter (only `items` and `keys` may move: no nested `Revoke` or `Recover`; mvcc's
`delsLs` meets it); while the transaction is open, it holds the batch transaction's lock
(`beTxHeld`, lent to the lessor for its bucket delete); `td.End()` (run under `le.mu`: a call into
the lessor there may only block) ends it with the caller's `Q`. Mvcc (3e)
proves it for its deleter (`s.Write(...)`); the applier (3a) passes it to `Revoke`. -/
def rdOk (γ : Names) (rd : GoFunc) (n : Nat) (ls : LessorState) (P : IProp GF)
    (D : GoInterface → List Key → Nat → LessorState → IProp GF)
    (Q : List Key → Nat → LessorState → IProp GF) : IProp GF :=
  iprop(
    {{ P }} (App (Val #rd) (Val #())) {{ (td : GoInterface), RET #td; D td [] n ls }} ∗
    (□ ∀ (td : GoInterface) (ks : List Key) (n' : Nat) (ls' : LessorState) (kb : GoSlice)
        (k : Key),
      {{ D td ks n' ls' ∗ lessorState γ n' ls' ∗ kb ↦* k }}
        (App (App (Val (td @!! go_etcd_io.etcd.server.v3.lease.TxnDelete.ty @!! go!"DeleteRange"))
          (Val #kb)) (Val #slice.nil))
      {{ (r1 r2 : w64), RET (PairV #r1 #r2);
          ∃ (n'' : Nat) (ls'' : LessorState), D td (ks ++ [k]) n'' ls'' ∗ lessorState γ n'' ls'' ∗
            ⌜ls''.leases = ls'.leases ∧ ls''.bkt = ls'.bkt ∧ ls''.be = ls'.be ∧ ls''.rd = ls'.rd⌝ }}) ∗
    (□ ∀ (td : GoInterface) (ks : List Key) (n' : Nat) (ls' : LessorState),
      D td ks n' ls' -∗ beTxHeld ls.be ∗ (beTxHeld ls.be -∗ D td ks n' ls')) ∗
    (□ ∀ (td : GoInterface) (ks : List Key) (n' : Nat) (ls' : LessorState),
      {{ D td ks n' ls' }}
        (App (Val (td @!! go_etcd_io.etcd.server.v3.lease.TxnDelete.ty @!! go!"End")) (Val #()))
      {{ RET #(); Q ks n' ls' }}))

/-- **What a receive from the expiry channel gives** (persistent): the slice `sl` (read-only) of
`*Lease` objects of leases `ids` (in order; each the lessor's at some point: it may be revoked by
the time the receiver acts). -/
def expiredSl (γ : Names) (sl : GoSlice) (ids : List Int) : IProp GF :=
  iprop(∃ ps : List Loc, sl ↦*□ ps ∗ ⌜ps.length = ids.length⌝ ∗
    [∗list] pi ∈ ps.zip ids, ∃ ttl, leaseObj γ pi.1 pi.2 ttl)

end res

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def persistent.spec : Prop :=
  (∀ le γ c, Persistent (isLessor (GF := GF) le γ c)) ∧
  (∀ γ n ls, Persistent (lessorAt (GF := GF) γ n ls)) ∧
  (∀ γ l id ttl, Persistent (leaseObj (GF := GF) γ l id ttl)) ∧
  (∀ γ c ch, Persistent (expiredCh (GF := GF) γ c ch)) ∧
  (∀ le R, Persistent (ckptGate (GF := GF) le R)) ∧
  (∀ be Pk f, Persistent (beHook (GF := GF) be Pk f)) ∧
  (∀ cl, Persistent (clusterOk (GF := GF) cl))

def timeless.spec : Prop :=
  (∀ γ n ls, Timeless (lessorState (GF := GF) γ n ls)) ∧
  (∀ γ n ls, Timeless (lessorAt (GF := GF) γ n ls)) ∧
  (∀ γ l id ttl, Timeless (leaseObj (GF := GF) γ l id ttl))

def exclusive.spec : Prop :=
  (∀ γ n n' ls ls', lessorState (GF := GF) γ n ls ∗ lessorState γ n' ls' ⊢ iprop(False)) ∧
  (∀ le, lessorStop (GF := GF) le ∗ lessorStop le ⊢ iprop(False)) ∧
  (∀ le, lessorCkptTok (GF := GF) le ∗ lessorCkptTok le ⊢ iprop(False))

/-- **A lessor is a non-`nil` pointer** (mvcc's `delete` calls `s.le.GetLease` unconditionally and
`restore` dereferences it: 3e's item 1, `req/..._lease.md`, "from 3e"). -/
def isLessor_ne_null.spec : Prop := ∀ le γ c,
  isLessor (GF := GF) le γ c ⊢ ⌜le ≠ null⌝

/-- One lessor has one ghost name and one configuration (3a's request, integration I5: the
apply's `lessorOk` and `lessorSt` each name the lessor's `γ`; the realization's `isLessor`
includes the configuration's fields read-only (`le.minLeaseTTL ↦□ …`, so `c` agrees) and a
persistent ghost record `le ↦ γ` in a global ghost map from lessors to their names, so `γ`
agrees). -/
def isLessor_agree.spec : Prop := ∀ le γ γ' c c',
  isLessor (GF := GF) le γ c ∗ isLessor le γ' c' ⊢ ⌜γ = γ' ∧ c = c'⌝

/-- The current state is in the history. -/
def lessorState_at.spec : Prop := ∀ γ n ls,
  lessorState (GF := GF) γ n ls ⊢ lessorState γ n ls ∗ lessorAt γ n ls

/-- The history is a function of its index. -/
def lessorAt_agree.spec : Prop := ∀ γ n ls ls',
  lessorAt (GF := GF) γ n ls ∗ lessorAt γ n ls' ⊢ ⌜ls = ls'⌝

/-- The current state is the history's last. -/
def lessorState_le.spec : Prop := ∀ γ n ls i ls',
  lessorState (GF := GF) γ n ls ∗ lessorAt γ i ls' ⊢ ⌜i ≤ n⌝

/-- A live lease's object, in any state of the history. -/
def lessorAt_obj.spec : Prop := ∀ γ n ls id (e : LeaseEnt),
  lessorAt (GF := GF) γ n ls ∗ ⌜ls.leases id = some e⌝ ⊢ leaseObj γ e.obj id e.ttl

/-- **Every state's TTLs are at least the minimum** (only `grant` and `loaded` set TTLs, both
through `grantTTL`). -/
def lessorAt_minTTL.spec : Prop := ∀ le γ c n ls,
  isLessor (GF := GF) le γ c ∗ lessorAt γ n ls ⊢
    ⌜∀ id (e : LeaseEnt), ls.leases id = some e → c.minTTL ≤ e.ttl⌝

/-- **The writer lends a reader token** (for its own reads: `Lookup`, `GetLease`, `Keys`). -/
def lessorState_reader.spec : Prop := ∀ γ n ls,
  lessorState (GF := GF) γ n ls ⊢
    lessorReaders γ 1 ∗ (lessorReaders γ 1 -∗ lessorState γ n ls)

/-- **The reader tokens split and join.** -/
def lessorReaders_split.spec : Prop := ∀ γ n m,
  lessorReaders (GF := GF) γ (n + m) ⊣⊢ lessorReaders γ n ∗ lessorReaders γ m

/-- **No checkpointer, for good**: give up the right to set one. -/
def lessorCkptTok_gate.spec : Prop := ∀ le,
  lessorCkptTok (GF := GF) le ⊢ ckptGate le iprop(True)

/-- A lease object's `ID` field, read-only for good; its id fits an `int64`. -/
def leaseObj_id.spec : Prop := ∀ γ l id ttl,
  leaseObj (GF := GF) γ l id ttl ⊢
    l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"ID"] ↦□ (W64 id) ∗
    ⌜l ≠ null ∧ -2 ^ 63 ≤ id ∧ id < 2 ^ 63 ∧ -2 ^ 63 ≤ ttl ∧ ttl < 2 ^ 63⌝

/-- An object was live: every object the lessor hands out is one some state of its history had
live (made by `Grant` or loaded). -/
def leaseObj_live.spec : Prop := ∀ γ l id ttl,
  leaseObj (GF := GF) γ l id ttl ⊢
    ∃ (j : Nat) (ls : LessorState) (e : LeaseEnt), lessorAt γ j ls ∗
      ⌜ls.leases id = some e ∧ e.obj = l ∧ e.ttl = ttl⌝

/-- An object is of one lease. -/
def leaseObj_agree.spec : Prop := ∀ γ l id id' ttl ttl',
  leaseObj (GF := GF) γ l id ttl ∗ leaseObj γ l id' ttl' ⊢ ⌜id = id' ∧ ttl = ttl'⌝

/-- **The writer lends the lease bucket** (e.g. to close the backend at shutdown): it is `ls.bkt`,
and the token comes back with it unchanged. -/
def lessorState_bkt.spec : Prop := ∀ γ n ls,
  lessorState (GF := GF) γ n ls ⊢
    beLeases ls.be ls.bkt ∗ (beLeases ls.be ls.bkt -∗ lessorState γ n ls)

/-- **The writer lends the backend's open share** (the server's shutdown hands it to the backend's
`Close`; the token comes back with it). -/
def lessorState_beOk.spec : Prop := ∀ γ n ls,
  lessorState (GF := GF) γ n ls ⊢ beOk ls.be ∗ (beOk ls.be -∗ lessorState γ n ls)

/-- **The expiry channel's receive** (`run`'s `select` arm): with the expiry mode on, expired leases'
objects (`expiredSl`); with it off, nothing is ever received (the trusted premise
`leasesOutliveRun` taken at `NewLessor`). The channel is never closed. -/
def expiredCh_recv.spec : Prop :=
  ∀ (γ : Names) (c : Cfg) (ch : GoChan) (Φ : GoSlice → Bool → IProp GF),
    expiredCh (GF := GF) γ c ch ⊢
      ∃ (_ : Pos.Countable GoSlice) (γc : ChanNames),
        isChan ch γc GoSlice ∗
        (£ 1 ∗ £ 1 -∗ (▷ ∀ sl, (∃ ids, ⌜c.expiry = true⌝ ∗ expiredSl γ sl ids) -∗ Φ sl true) -∗
          recvAu γc GoSlice Φ)

/-- The package's errors: distinct non-nil values (each its own package variable). -/
def init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ⊢
    ∃ e1 e2 e3 e4 : GoInterface,
      errIs go_etcd_io.etcd.server.v3.lease.ErrNotPrimary e1 ∗
      errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound e2 ∗
      errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseExists e3 ∗
      errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseTTLTooLarge e4 ∗
      ⌜[e1, e2, e3, e4].Nodup ∧ ∀ e ∈ [e1, e2, e3, e4], e ≠ GoInterface.nil⌝

end laws

end Lease
end EtcdGrove
end Perennial
