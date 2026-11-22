/-
`lease.NewLessor(lg, b, cluster, cfg)` (`lessor.go`): names-only (it recovers the lessor from the
backend and starts the lessor's loop). Lean-first (no Rocq counterpart); the server-construction
unit, stage N0 (2026-10-16, D13: `notes/decisions.md`), for `NewServer`; an axiom at the trust
boundary from unit N4 (2026-10-17, D14d/D14f/D14g) to prove-ps2-newlessor5 (2026-11-21), why it is true
of the Go code below; now proved over the real code (`Proof/.../lease/NewLessor.lean` over `newLessor`),
the expiry loop's payload `¬ leasesNoExpiry` resting on `Lease.expired`'s axiom
(`notes/axiom-review/lease-expired-payload.md`).

(mvccfull's Freeze, 2026-11-10) Over a `Lease` bucket holding records (a restart: a member's backend
reopened on its file), for etcd's server restart (`notes/restart-plan.md`, R2d'b) and the tester
`examples/mvccfull` (`runner.open` after `shut`); until then on an empty bucket only (the statement at
commit `ae30739dde`, the instance at `recs = []`). Reviewed (`notes/review/mvccfull-f1-newlessor-r1.md`)
and attacked (`notes/axiom-review/mvccfull-newlessor-specR.md`) before the Freeze.

**The receipt `⧖ |recs|`** (review round 1's F1; settled by the axiom review,
`notes/axiom-review/mvccfull-newlessor-specR.md`: kept). The post's `lessorInv` holds `lessorMu`'s
`⧖ (size M)` (`InvLessor.lean`), so at the recovered map (`M = recMap (recs.zip ls)`) this axiom
gives out the receipt `⧖ recs.length`, which the original (at `M = ∅`, `⧖ 0`) never did. Its source
is the translated code: `NewLessor` → `newLessor` → `initAndRecover`, and the proved
`lessor.initAndRecover.spec` (`Spec/.../lease/lessor__initAndRecover.lean`) has `⧖ recs.length` in
its post with no receipt in its pre (its proof starts from `preceipt_zero` and raises the receipt
once per iteration of the recovery loop, `lessor.go:815-830`: `wp_raise_receipt`). So the receipt
is what the translation of the same Go code proves; the axiom adds only `newLessor`'s names-only
wrapper (its fields, the reader slots, the `runLoop` goroutine), not the step count. The per-lease
allocations (`make(chan struct{})` for `revokec`, the zero `RWMutex` of `&Lease{}`, inside
`leaseOwn`'s closers) are `initAndRecover`'s too. (The alternative, the receipt in the pre, would be
strictly weaker for clients and cost the server a law, `recs.length ≤ logCh L` of the image, for no
soundness.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Recover

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewLessor(lg, b, cl, cfg)` over a `Lease` bucket holding the records `recs`**: everything
the empty bucket's statement says (the clauses below), except that the
bucket, a part of any bucket set `S` containing it (`rbPart d.γB S r`), holds in key order the
records `recs`, each what `Grant` writes (`backend.bktEnts … = recs.map leaseRecEnc`, `Recover`'s
premise; empty or absent: `recs = []`, the original; a scope restriction, as `Recover`'s: only
buckets whose every value is exactly `leaseRecEnc` of a record, `proto.Marshal` of the three fields;
a bucket written by another tool, or a record with unknown fields, which Go would decode, is
outside it), and what the lessor makes of them is what
`Recover` makes (`lessor.Recover.spec`), at a lessor that had nothing before (`L = []`, `U = []`).
The new clauses, and why each is true of the Go code (`newLessor` `lessor.go:212-249`,
`initAndRecover` `:808-835`):
* **The records are read and decoded** (pre: the entries' equation, replacing `getD ∅ = ∅`):
  `initAndRecover` takes the batch lock (`:811`), creates the bucket (absent: none; present: a
  no-op, `UnsafeCreateLeaseBucket`), and `MustUnsafeGetAllLeases` (`:813`) decodes every record
  (a panic on an undecodable one; each record here is an encoding, `leaseRecEnc`, so none). Two
  write-back tokens (`ownToks d.γB.wb 2`, as `lessor.Recover.spec`; prove-ps2-newlessor3,
  2026-11-21, the user's approval: until then one, `wbTok`, which no proof over the real code can
  meet, since the proved `lessor.initAndRecover.spec` takes two), with records as without: `UnsafeCreateBucket` always counts a pending
  operation (`pending++`, `batch_tx.go:144`), so the first `Unlock` (`:814`) writes back
  (`batch_tx.go:328-333`) and may commit (`pending >= batchLimit`, `:355`); `ForceCommit`
  (`backend.go:377`) is `lock`, `commit`, `Unlock` (`batch_tx.go:362-366`), and `commit` resets
  `pending = 0` (`:300`), so its `Unlock` writes nothing back (a hook the commit runs may write;
  `commit` still resets `pending`). The records change neither `pending` nor the commits (the loop
  writes no bucket). The second token pays `ForceCommit`, whose proved `backend.ForceCommit.spec`
  charges one although its `Unlock` writes nothing back (the backend's spec is coarser than the
  code). So the part comes back idle with the bucket as it was
  (`rbOwnIn d.γB S (r.insert "lease" ((r.lookup "lease").getD ∅))`, `Recover`'s post; the
  original's `r.insert "lease" ∅` when it was empty or absent).
* **One fresh lease per record** (`:815-830`): `ID` the record's, `ttl` the record's raised to
  `le.minLeaseTTL`, which `newLessor` set to `cfg.MinLeaseTTL` (`:231`, never written again: the
  post's `lF "minLeaseTTL" lp ↦□ cfg.MinLeaseTTL'`, review round 1's S2, which ties `lessorCfg`'s
  minimum, the one a later `Grant` raises to, to the recovered TTLs'), no item, `expiry` forever,
  a fresh `revokec`, `remainingTTL` the record's, put into the fresh `leaseMap` (no registration
  with the expiry notifier, `Init` of an empty one; the heap empty). So the live set is the
  records' ids in the caller's order `Lr` with no item (`leaseOwn γl Lr ∅`, the original's
  `leaseOwn γl [] ∅` at `recs = []`), each with its close right (`leaseRevokers γl Lr`): what
  `Recover`'s post gives for the same loop. The ids are distinct (the bucket's keys are, and a
  record's key is its id's 8 bytes).
* **The history's first snapshot is the recovered one** (ghost state only): the readers' model is
  allocated (as in the original) at the single snapshot `(recMap (recs.zip ls), ∅, recTTLs
  cfg.MinLeaseTTL' recs)` (the leases `ls` above; their TTLs the raised ones, each lease's `ttl`
  field, written before the map insertion and never after: `ttlTie`), the item sets' map at the
  new leases' empty sets; its facts hold of one snapshot (`histOk`: one id per lease, no item;
  `histMono`, `histOnce` trivially; `histIn`/`histCover` of the records' ids). The caller gets its
  index, `0` (`lessorAt γl 0 _`; at `recs = []` the original's `lessorAt_empty` derives it).
* **The ids the lessor ever had** (`leaseEver γl (recs.map (·.1))`): allocated at the records'
  ids, which the first snapshot has (`histIn`, `histCover`); at `recs = []`, the original's `[]`.
  Ghost state, allocated fresh with the readers' names: the caller gives nothing for it (a fresh
  lessor never had an id; `Recover`'s premises on `U` hold at `U = []`).
* **The leases' requested TTLs** (`□ leaseReqIs γl x.1 (reqOf x.1)`, the caller naming each
  record's request `reqOf`, at most its TTL): the requests' map allocated at those requests, not
  empty; `reqOk` holds since each first-snapshot TTL is the record's raised (`grantTTL`), at least
  the record's, at least the request. Persistent discarded elements: no counted resource.
* **The grant guard** (pre: `□ GA id` for every record's id): every lease of the map has the
  guard of its id (`lessorAuth`'s `leaseGranted`, `Lookup`'s and `expiredC`'s `□ GA id`); the
  original's map starts empty, so it needed none; here the caller gives it (`Recover` takes it,
  as `leaseGranted`, for the same reason). Persistent.
* **The mode** `mono`: as the original; a single snapshot is monotone (`histMono`), so either mode
  holds with records too (`Recover`'s mode premise, live ids among the records', is vacuous at
  `L = []`).
Everything else, the `runLoop` goroutine (`:245`) and what the post says of it (`lessorExpiredC`,
`lessorGuard`), the configuration, the reader slots, `rd`
unset, `lessorBeOn`/`lessorApplyOk`, the stop right, is the original's, word for word: the loop
does not read the bucket, and every lease it sends is the map's, with `GA` of
its id by the guard clause above.

**The empty bucket's clauses** (the statement until the Freeze; "the original" above), and why
each is true of the Go code: **`NewLessor(lg, b, cl, cfg)`** over the real backend `d` (`b` its `*backend`; D14d): the
lessor at `lp` (`lessorInv`, its configuration and `expiredC`, a reader slot of its lock for the
store, the live set empty), and the contract of its backend for the
lessor's writes (`lessorBackend`), at the backend's batch lock `Pk` and any frozen post-lock hook
`f`, with one write-back token per write and the reader's open share lent (D14f). The `Lease`
bucket is in the backend's table, tracked, none of its keys a hook's (`mvcc.leaseParams d.P`, a
boot fact; 2026-11-01, E: so the bucket it creates is among the backend's ghost names `γ.rbD`, as
`rbOwnIn` of the result needs); a part of any bucket set `S` containing it comes back idle
(`rbPart d.γB S r` in, `rbOwnIn d.γB S (r.insert "lease" ∅)` out).

Why it is true of the Go code (`newLessor`, `initAndRecover`, `runLoop`, at the etcd pin):
* `newLessor` allocates the lessor (its maps, `expiredC` a channel of 16, `stopC`, `doneC`), sets
  the configuration's fields (a zero `leaseRevokeRate` defaulted to 1000: so a positive rate, given
  a non-negative one, `lessorCfg`; audit B4b, 2026-10-18; and the logger `lg` as given, which the
  pre asks to be nil or a zap logger, `zapLoggerOk`, and `lessorCfg` keeps: the lessor logs only
  under `le.lg != nil` (`lessor.go:759,797`), and a non-nil zero `&zap.Logger{}` panics in its
  `Debug`; the user's decision of 2026-11-07, sweep B3-2: until then the pre asked only
  `lg ≠ null`), then `initAndRecover`:
  `b.BatchTx()`'s `LockOutsideApply` (no hook: the backend open, `bOpen`), `UnsafeCreateLeaseBucket`,
  `MustUnsafeGetAllLeases` (it decodes every record of the `Lease` bucket, a panic on an
  undecodable one: the bucket is empty, a part of any bucket set `S` containing `lease`,
  `backend.rbPart d.γB S r`, says so; `MustUnsafeGetAllLeases` reads through the batch transaction,
  the writer's contents, which the part names; D22, 2026-10-23: until then the opaque token
  `bkFresh d.γB "lease"`, consumed; the creation needs the part, given back with the bucket present
  and empty), `Unlock` (one write-back: the token; after it the readers see the writer's contents
  on every bucket, the Go basis: the part **idle**, `rbOwnIn`, `TestBksNewLessorIdle`), the heap's
  `Init`, and `b.ForceCommit()`, which commits first so its `Unlock` finds nothing pending and does
  not write back (the backend's `ForceCommit.spec` charges a token: the spec is coarser than the
  code). Its commit runs the backend's hooks (`isBackend`). So the live set is empty (`leaseOwn γl
  [] ∅`), and so is the item map (`le.itemMap`, made by `newLessor`: the lock holds half of it, the
  caller the other half, unit T3, L2b), with no lease to revoke (`leaseRevokers γl []`).
  (2026-11-01, the backend-auth-split stage: until then the whole writer's half `rbOwn`, in and out.)
  The range deleter `rd` is unset (`nil`): `newLessor` does not set it, and the caller owns the
  half of the field that the lock does not hold (`rdOwn γl func.nil`, unit T3). The checkpointer
  `le.cp` is `nil` (`lessorExtra`; stage B3, 2026-11-12): `newLessor` does not set it
  (`lessor.go:225-242`), and the model has no contract for `SetCheckpointer`, its only writer
  (`lessor.go:274-279`), which `NewServer` calls only with the `LeaseCheckpoint` feature on
  (`server.go:393-405`; `NewServer.spec` takes it off). (Until then the post also gave
  `lessorCkptOk`, a contract for `SetCheckpointer`.)
* `go l.runLoop()`: until the lessor is promoted it only takes its lock, finds no expired lease
  and no due checkpoint; once promoted it sends expired leases on `expiredC` (the server's `run`
  receives them) and would call the checkpointer if one were installed; with `cp` nil (above),
  `findDueScheduledCheckpoints` returns `nil` (`lessor.go:772-775`) and nothing is proposed (until
  2026-11-12 the pre took the opaque `ckptEffectsOk` for these calls; deleted, as they never happen). **The grant
  guard** (D19n, 2026-10-18): the caller picks a predicate `GA` on lease ids, saved and pinned in
  the lessor's ghost map (`lessorGuard γl GA`); `Grant` adds a lease only with `leaseGranted`
  (`GA` of its id, under the guard), which the lock keeps for every lease of the map
  (`lessorAuth`). The loop's `revokeExpiredLeases` sends on `expiredC` only a non-empty slice
  (`if len(ls) != 0`, `lessor.go:652`) of leases `findExpiredLeases` took from `leaseMap` under the
  read lock (`expireExists`: `le.leaseMap[item.id]`, `nil` skipped, `lessor.go:706`), so every lease
  of it has `GA` of its id (the guard agrees with the saved one, after a step): `expiredC`'s
  predicate (`lessorExpiredC lp GA`). (The lease-expiry plan's X3, 2026-11-04; until then `∃ id,
  GA id`) The slice is the loop's own, never written after the send (`ls ↦*□ ps`, `ps ≠ []`), its
  elements the map's non-null `*Lease`s, each `ID` set by `NewLease` and never written again
  (`lsF "ID" p ↦□ id`), each with `GA id` (`expiredLeases GA`). The map starts empty (the fresh `Lease`
  bucket; `Recover`, not called, would reload it).
* The backend's contract (`lessorBackend lp Pk f T Ln R Rb`, used by `Grant` and `Checkpoint` through
  `Lease.persistTo`): `BatchTx()` returns the batch transaction; `LockInsideApply` needs the
  backend open (a share of `bOpen`, in the reader's token `mvcc.bkRTx`, lent) and runs the frozen
  hook `f` under `Pk` (`csContract Pk f`); `UnsafePut` into the `Lease` bucket (created by
  `initAndRecover`; a hook bucket, `bridgeParams`, so the readers' view is unchanged) of an
  8-byte key never fails; `Unlock` writes back at most once (`wbTok`). The `Lease` bucket is a
  tracked bucket (D22, 2026-10-23: `KBReal.P`'s `RB`): the put takes the lease bucket's part
  (`backend.rbPart d.γB (· = "lease")`, the backend's `UnsafePut` of a tracked bucket, per bucket:
  `rbPut`; 2026-11-01, the backend-auth-split stage: until then the whole client half `rbOwn`) and
  gives it back with the entry put (`mvcc.rbSet r "lease" k v`; leases T3, L3c, 2026-10-27: until
  then each write took the half, `srvRestRW d.γB`, in its write right, and the put's effect was not
  stated); the lock and `Unlock` do not need it.
  (D22 receiver epochs, S7c, 2026-10-23) The lessor's lock holds half of `le.b`
  (`lessorExtra`), the caller gets the other (`lease.lessorBeOn lp d.be`); `persistTo(le.b)`
  reads it under the lock, so the writes go to the backend the caller's half names: the contract
  (`lessorApplyOk`; prove-ps2-newlessor5, 2026-11-21: at a backend whose parameters have the `Lease`
  bucket, `mvcc.leaseParams`, whose `UnsafePut` would otherwise be a `Fatal`, one put per lock, all
  `persistTo` does; proved of the real backend, `lessorApplyOk_real`) is for whichever backend that is (its contract at some `W`, `Pk`, its frozen
  hook), given a write right lending that half of `le.b` (`rwLens`), which a write gives back (the
  lease-grant stage, 2026-11-02: the lent part `Ln`, apart from the spent token); `Recover`
  (names-only) replaces both halves under the lock. Until S7c `le.b` was `↦□` and the contract for
  `d` only, which `Recover` refutes.
* (Deleted, prove-ps2-newlessor5, 2026-11-21, the main session's decision under the user's rule) The
  token-free `Lookup` clause (`{{ True }} lp.Lookup(id) {{ … }}`, unit N4, D14h, 2026-10-17): the code
  read-locks `mu`, which the model's `RWMutex` bounds by reader slots, so no proof over the real code
  gives it without a slot or a token; no proof used it (it went to `isApplyLessor`'s `Lookup` clause,
  deleted with it; a reader calls `Lookup` through `lessor.Lookup.spec`, with its slot).
* **The thread bound** (`⌜threadBound GF ≤ 2 ^ 30 - 1⌝`; prove-ps2-newlessor3, 2026-11-21, the
  user's approval): the `runLoop` goroutine's `findExpiredLeases` calls `l.expired()`, whose
  `Remaining()` read-locks the lease's `expiryMu` (`lease.go`), borrowing a slot from the lease's
  pool (`isLeaseObj`), which exists only under this bound (as `Renew`'s, `Promote`'s, `Leases`').
  Every caller has it (the server's construction and the examples bound threads by `2 ^ 28` or
  `2 ^ 29`).
* The reader slots of `mu` (a `sync.RWMutex`, made by `newLessor`): one per reader (D14i,
  2026-10-17: the store's and the apply thread's lease owner each hold one). All of them but one
  (prove-ps2-newlessor, 2026-11-21, the user's approval): the `runLoop` goroutine read-locks `mu`
  in every iteration (`revokeExpiredLeases`, `lessor.go:640`) and keeps one slot for its lifetime.
  Until then the post gave all `Int.toNat actualMaxReaders` slots to the caller, one more than
  `init_RWMutex` makes once the loop has its own: false of the model
  (`notes/axiom-review/newlessor-reader-slot.md`).
* (lease-keys Part B, 2026-10-31) **The readers' model** (`lessorRdInv`, in `lessorInv`), ghost
  state only: allocated before `γl`'s element, which pins its names (`lessorPinR`), it is the
  lessor's history at the single snapshot `(∅, ∅)` (the fresh `leaseMap` and `itemMap`, empty as
  above), split a quarter to the invariant `lessorRdN`, a quarter to the lock (`lessorMu`, at the
  whole lock's fraction) and a half to the owner (`leaseClosers`), and the item-sets map empty, its
  authority halved between the invariant and the owner; the invariant's `setsOk [(∅, ∅)] ∅` and
  `histOk [(∅, ∅)]` hold trivially (no lease, no key). No Go state is read or written for it.
* (The lease-grant plan's D2, 2026-11-02) **The mode** (`lessorModeIs γl mono`), chosen by the
  caller and pinned with the readers' names: monotone (`mono = true`), the invariant also keeps
  `histMono` (trivial of the single snapshot), and `Revoke` and `Recover`, which take the other
  mode (`lessorRevocable`), are not called. Ghost state only.
* (The lease-expiry plan's E3 (c), route A, the user's approval 2026-11-05) **The ids the lessor
  ever had** (`leaseEver γl []`), ghost state only: a ghost variable at `[]`, allocated with the
  readers' names (their fourth, `γr.2.2.2.1`), halved between the readers' invariant (which also
  keeps `histOnce` and `histIn` of the single empty snapshot, and (the S2–S4 Probe, 2026-11-05)
  `histCover` of `[]`, trivially) and the caller.
* (The lease-expiry plan's S2–S4, Q-S6 (A-ii), the user's approval 2026-11-05) **The leases'
  requested TTLs** (`leaseReqIs`), ghost state only: a ghost map, allocated empty with the readers'
  names (their fifth, `γr.2.2.2.2.1`), its whole authority in the readers' invariant, which keeps
  `reqOk` of the single empty snapshot and the empty map trivially (no lease, no TTL, no request).
  Allocatable because a fresh ghost map at `∅` is (`ghost_map_alloc`), before `γl`'s element pins
  the names. It makes no claim about Go: no Go state is read or written for it, and nothing about
  `NewLessor`'s code depends on it; `Grant` and `Recover` (proved) are what insert requests and keep
  every TTL above them.
* (Auth-lease S4 item 7b, decided by etcd-grove-03 2026-11-17, `questions.md` "Item 7b step 1") **The
  windows** (`lessorWinTie γl []`, `winsOk`, `itemsLive`), ghost state only: a mono-list allocated at `[]`
  (`mono_list_own_alloc`) with the readers' names (their sixth, `γr.2.2.2.2.2.1`; the requests map is their fifth's
  first, `γr.2.2.2.2.1`), its authority split a half to the readers' invariant, a quarter to the owner (`leaseOwn`'s
  closers, whose open window `lastWin [] = none` is `leaseOwn`'s), a quarter to the caller (`lessorWinTie`). The
  invariant's `winsOk hs []` holds of any history (no window), and `itemsLive` of the single initial snapshot, whose
  item map is empty. No Go state is read or written for it; `Attach`, `Detach`, `Grant`, `Revoke` and `Recover`
  (proved) keep the facts at every push.
* (2026-11-04, R2b-3c part 2, the user's approval) **The right to stop it** (`lessorStopTok lp`,
  for `lessor.Stop`): `newLessor` makes `stopC`, which only `Stop` closes; one right, given here.
  (prove-ps2-lease, 2026-11-21: until then an opaque axiom; now a definition, `LessorBackend.lean`.)
  What it claims, and why it is true: `stopC` and `doneC` are fresh unbuffered channels
  (`make(chan struct{})`, `lessor.go:238-239`), fields written only by the struct literal, so
  read-only (`lF "stopC" lp ↦□ c`, `lF "doneC" lp ↦□ d`), nothing is ever sent on either.
  `stopC` is a close-once channel (`onceRecv`, since prove-ps2-renew, 2026-11-21; until then a
  broadcast channel whose `.Pending` the caller got): the caller gets its close token (`Stop`'s
  `close(le.stopC)` is the only close, a second would panic); the lessor keeps its receive side
  (`lessorStopRecv`, persistent) for `runLoop`'s `select` and `revokeExpiredLeases`'
  (`lessor.go:632,654`) and `Renew`'s (`:426`). `doneC` is a broadcast channel (Perennial's
  `alloc_broadcast_chan`, ghost state only, at `Q = True`): its close right goes to the `runLoop` goroutine, whose deferred
  `close(le.doneC)` (`:621`) is the only close of it; the caller gets its receive side
  (`.Unknown`). So nothing of the Go code is assumed beyond what the original opaque right said.
* (prove-ps2-lease, 2026-11-21) **`demotec`** (inside `lessorInv`: `lessorExtra`'s `demoteTie`, at the
  readers' names' seventh, `γr.2.2.2.2.2.2.1`): `newLessor` leaves `demotec` nil (the struct literal
  names no `demotec`, `lessor.go:225-242`), so a ghost variable allocated at `chan.nil`, half in the
  lock's guard, half in the invariant `demoteOuter` (allocated here, at `nil`: its left disjunct).
  Ghost state only; `Promote` and `Demote` (both proved) keep it. -/
abbrev lease.NewLessor.spec : Prop :=
  ∀ (lg : Loc) (cl : GoInterface) (cfg : go_etcd_io.etcd.server.v3.lease.LessorConfig)
    (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp) (GA : w64 → IProp GF)
    (S : GoString → Prop) (r : GMap GoString backend.BktData) (mono : Bool)
    (recs : List (w64 × w64 × w64)) (reqOf : w64 → w64) (Lr : List w64),
  S go!"lease" → mvcc.leaseParams d.P →
  backend.bktEnts ((r.lookup go!"lease").getD ∅) = recs.map lease.leaseRecEnc →
  (∀ x ∈ recs, sint.Z (reqOf x.1) ≤ sint.Z x.2.1) → Lr.Perm (recs.map (·.1)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      (⌜lg = null⌝ ∨ zapLoggerOk lg) ∗
      ⌜0 ≤ sint.Z cfg.leaseRevokeRate'⌝ ∗ lease.clusterOk cl ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ ownToks d.γB.wb 2 ∗
      backend.rbPart d.γB S r ∗ □ ([∗list] id ∈ recs.map (·.1), GA id) ∗
      ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.NewLessor)) (Val #lg))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
      (Val #cl)) (Val #cfg))
  {{ (l : GoInterface), RET #l; backend.bOpen d.γB qo ∗
      backend.rbOwnIn d.γB S (r.insert go!"lease" ((r.lookup go!"lease").getD ∅)) ∗
      ∃ (lp : Loc) (γl : GName),
      ⌜l = lease.lessorIface lp⌝ ∗ lease.lessorInv lp γl ∗ lease.lessorModeIs γl mono ∗
      lease.lessorCfg lp ∗ lease.lF go!"minLeaseTTL" lp ↦□ cfg.MinLeaseTTL' ∗
      lease.lessorExpiredC lp GA ∗ lease.lessorGuard γl GA ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1) (), lease.lessorRdOf γl) ∗
      lease.leaseOwn γl Lr ∅ ∗ lease.lessorWinTie γl [] ∗ lease.leaseEver γl (recs.map (·.1)) ∗
      lease.leaseRevokers γl Lr ∗
      lease.rdOwn γl func.nil ∗
      lease.lessorBeOn lp d.be ∗ lessorApplyOk lp ∗
      lease.lessorStopTok lp ∗
      □ ([∗list] x ∈ recs, lease.leaseReqIs γl x.1 (reqOf x.1)) ∗
      (∃ ls : List Loc, ⌜ls.length = recs.length⌝ ∗
        lease.lessorAt γl 0 (lease.recMap (recs.zip ls), ∅, lease.recTTLs cfg.MinLeaseTTL' recs)) }}

end spec

end EtcdGrove
end Perennial
