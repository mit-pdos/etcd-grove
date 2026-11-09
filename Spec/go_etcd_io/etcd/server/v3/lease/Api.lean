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
  `specs-ref`'s axiom sweep B3-2), its cluster (`clusterOk`), its checkpointer (nil or `ckptOk`), its
  expiry channel's protocol, its run loop.
* `lessorState γ n ls` (exclusive, timeless): **the writer's token: the lessor's state is `ls`, the
  `n`-th of its history**. Every method that changes the state takes it (the apply thread holds it;
  mvcc's writes and the range deleter borrow it from there). The lease bucket of `ls.be` is inside it
  (`lessorState_bkt` lends it out).
* `lessorAt γ n ls` (persistent, timeless): **the lessor's `n`-th state was `ls`** (its history: every
  state a writer's step produced). Readers (`Lookup`, `Leases`, `GetLease`, `Keys`, `Renew`) take
  `lessorAt γ i _` (a lower bound) and answer from a state `j ≥ i` of the history, which they return
  (`lessorAt γ j ls'`): a writer, holding `lessorState γ n ls` and passing `lessorAt γ n ls`, gets
  `j = n` (`lessorState_le`, `lessorAt_agree`), so one spec serves both. The server (2d) ties the
  history to its own (`histAt`): which lessor state each applied entry ends at.
* `leaseObj γ l id ttl` (persistent): `l` is a `*Lease` object of this lessor, of lease `id` and
  granted TTL `ttl` (its `ID` and `ttl` fields never change after it is published).
* `lessorStop le` (exclusive): the right to `Stop()` (a second `Stop` closes `stopC` twice).
* `expiredCh γ c ch` (persistent): `ch` is the lessor's expiry channel; `expiredCh_recv` is its
  receive.
* `rdOk`, `ckptOk` (transparent): the contracts of the two callbacks the lessor calls (the range
  deleter for `Revoke`, the checkpointer for `Renew` and the run loop).
* Provisional, other batches' (to be replaced by theirs at integration): `beOk be`, `beLeases be B`,
  `beApplyTok be`, `beTxHeld be` (4a/4b, `req/go_etcd_io_etcd_server_v3_storage_backend.md` and
  `..._schema.md`, "from 3c"); `clusterOk cl` (2e's membership, `RaftCluster.Version`).
* `leasesOutliveRun` (opaque `Prop`): **the trusted deployment premise about time** that no lease
  expires during the run (W0's `EnvCfg.leaseExpiry = false`, `top.md` K2). Taken by `NewLessor` for
  the expiry mode `false`; nothing proves it.

## Intended realization

`isLessor le γ c`: `le`'s read-only fields (`lg` with `isLogger`, `cluster` with `clusterOk`,
`minLeaseTTL = c.minTTL`, `checkpointInterval`, `expiredC`, `stopC`, `doneC`, `leaseRevokeRate`
positive), and `le.mu`'s invariant: the authority of a ghost variable `γ.cur` (`lessorState`'s other
half: the current `n`, `ls`) and of a `mono_list` `γ.hist` of the states (`lessorAt` its fragments),
with the Go maps at `ls` (`leaseMap` the live objects, `itemMap` at `ls.items`), `le.b = ls.be`,
`le.rd = ls.rd` (a half: the writer's token holds the other, since `Revoke` reads it unlocked), the
notifier and checkpoint heaps well-formed (`queueAt`), `demotec` with its close right, the lease
bucket `beLeases ls.be ls.bkt` (writes to it are under `le.mu`, by the writer), each live object's
`revokec` close right, and `le.cp` nil or with `ckptOk`. Each `*Lease`'s `mu` invariant holds its
`itemSet` at `ls.keys l` for the current state (by a ghost map `γ.keys`, object to set, its authority
in `le.mu`'s invariant beside the object's own lock: `Keys()` reads under `l.mu` alone);
`leaseObj γ l id ttl`: `l.ID ↦□ id`, `l.ttl ↦□ ttl`, the lock's invariant. `lessorState γ n ls`:
the ghost variable's writer half (with `le.rd`'s half). The run loop: holds `isLessor`; it sends live
objects on `expiredC` only with `c.expiry = true` (with `false`, an expiry found would contradict
`leasesOutliveRun`: the run loop's time reasoning is the trusted part, `runLoop` being untranslated).

## Laws

`persistent`, `timeless`, `exclusive`; `lessorState_at`, `lessorAt_agree`, `lessorState_le`,
`lessorAt_obj`, `leaseObj_id`, `leaseObj_live`, `leaseObj_agree`, `lessorState_bkt`, `expiredCh_recv`,
`init`.
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.lease
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.lease
public import Spec.go_etcd_io.etcd.api.v3.Model
public import Spec.go_uber_org.zap.Api
public import Spec.context.Api
public import Spec.google_golang_org.protobuf.proto.Api

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
lease this run's lessors hold expires during the run (every lease's TTL outlasts the run from its
last refresh). Opaque: nothing proves it; the program that starts the cluster takes it. -/
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

/-- `ch` is the expiry channel (`ExpiredLeasesC()`) of the lessor `γ` configured `c` (persistent). -/
opaque expiredCh (γ : Names) (c : Cfg) (ch : GoChan) : IProp GF := iprop(True)

/-- `le` as a `Lessor` interface value. -/
def lessorIface (le : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty) #le

/-- The lessor's error `g` (`ErrNotPrimary`, `ErrLeaseNotFound`, ...) is the value `e`. -/
def errIs (g : GoString) (e : GoInterface) : IProp GF := iprop(globalAddr g ↦□ e)

/-! ### Provisional: other batches' vocabulary -/

/-- (provisional, 4a's) **`be` is a backend** whose batch transaction may be fetched (`BatchTx()`),
locked outside an apply (`LockOutsideApply`, no hook), unlocked, and force-committed
(`ForceCommit()`) by any goroutine. Persistent. -/
opaque beOk (be : GoInterface) : IProp GF := iprop(True)

/-- (provisional, 4b's over 4a's) **The lease bucket of `be`, as its batch transaction holds it (the
last commit with the pending writes), decodes to `B`** (id to stored TTL; each record a
`leasepb.Lease` that unmarshals, so `MustUnsafeGetAllLeases` does not panic; its `RemainingTTL` not
modelled). Exclusive: its holder is the bucket's only writer (`MustUnsafePutLease`,
`UnsafeDeleteLease` move it, under the batch transaction's lock). -/
opaque beLeases (be : GoInterface) (B : Int → Option Int) : IProp GF := iprop(True)

/-- (provisional, 4a's) **The right to lock `be`'s batch transaction inside an apply**
(`LockInsideApply`, which runs the post-lock hook: the apply thread's, 2d's
`getTxPostLockInsideApplyHook`), given back at `Unlock`. Exclusive. -/
opaque beApplyTok (be : GoInterface) : IProp GF := iprop(True)

/-- (provisional, 4a's) **This thread holds `be`'s batch transaction lock** (an mvcc write
transaction is open: `Write()` locked it, `End()` unlocks it), so it may make unsafe writes.
Exclusive. -/
opaque beTxHeld (be : GoInterface) : IProp GF := iprop(True)

/-- (provisional, 2e's membership) **`cl` is a lessor's `cluster`**: `Version()` may be called from
any goroutine and returns `nil` or a readable `*semver.Version`. Persistent. -/
opaque clusterOk (cl : GoInterface) : IProp GF := iprop(True)

/-! ### The callbacks' contracts -/

/-- **The checkpointer's contract** (persistent): `cp(ctx, lc)` for any context and an owned
`*LeaseCheckpointRequest` returns `nil` or `ErrNotPrimary`. The lessor calls it with
`context.Background()` from `Renew` (which returns its error) and the run loop (which ignores it).
The server's closure (`NewServer`, `server.go:395`: `ErrNotPrimary` unless `ensureLeadership()`,
else `raftRequest` of the checkpoint, a no-op of W0's model, its error dropped, and `nil`) meets it.
The error set is restricted so that `Renew`'s errors are the lessor's own (2c's need). -/
def ckptOk (cp : GoFunc) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterface) (lc : Loc) (m : Proto.Content),
    {{ Context.ctxOk ctx ∗
        Proto.msgAt go_etcd_io.etcd.api.v3.etcdserverpb.LeaseCheckpointRequest.ty lc (DFrac.own 1) m }}
      (App (App (Val #cp) (Val #ctx)) (Val #lc))
    {{ (err : GoInterface), RET #err;
        ⌜err = interface.nil⌝ ∨ errIs go_etcd_io.etcd.server.v3.lease.ErrNotPrimary err }})

/-- **A range deleter's contract for one revocation** (transparent), from the writer's state `n`,
`ls` at the call: the caller's resource `P` lets `rd()` open a deletion transaction `td`, whose
client-side state `D td ks n' ls'` records the keys deleted so far and the lessor's state after
them; each `td.DeleteRange(k, nil)` borrows the lessor's writer token (mvcc's delete detaches the
key: its `GetLease`, `Detach`) and gives it back at some later state; while the transaction is open,
it holds the batch transaction's lock (`beTxHeld`, lent to the lessor for its bucket delete);
`td.End()` (under `le.mu`: it must not call the lessor) ends it with the caller's `Q`. Mvcc (3e)
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
          ∃ (n'' : Nat) (ls'' : LessorState), D td (ks ++ [k]) n'' ls'' ∗ lessorState γ n'' ls'' }}) ∗
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
  (∀ be, Persistent (beOk (GF := GF) be)) ∧
  (∀ cl, Persistent (clusterOk (GF := GF) cl))

def timeless.spec : Prop :=
  (∀ γ n ls, Timeless (lessorState (GF := GF) γ n ls)) ∧
  (∀ γ n ls, Timeless (lessorAt (GF := GF) γ n ls)) ∧
  (∀ γ l id ttl, Timeless (leaseObj (GF := GF) γ l id ttl))

def exclusive.spec : Prop :=
  (∀ γ n n' ls ls', lessorState (GF := GF) γ n ls ∗ lessorState γ n' ls' ⊢ iprop(False)) ∧
  (∀ le, lessorStop (GF := GF) le ∗ lessorStop le ⊢ iprop(False))

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

/-- The package's errors: distinct non-nil values, none of rpctypes'. -/
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
