/-
`lease.NewLessor(lg, b, cluster, cfg)` (`lessor.go`): names-only (it recovers the lessor from the
backend and starts the lessor's loop). Lean-first (no Rocq counterpart); the server-construction
unit, stage N0 (2026-10-16, D13: `notes/decisions.md`), for `NewServer`; an axiom at the trust
boundary since unit N4 (2026-10-17, D14d/D14f/D14g), why it is true of the Go code below.

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
  (a panic on an undecodable one; each record here is an encoding, `leaseRecEnc`, so none). One
  write-back (`wbTok`), with records as without: `UnsafeCreateBucket` always counts a pending
  operation (`pending++`, `batch_tx.go:144`), so the first `Unlock` (`:814`) writes back
  (`batch_tx.go:328-333`) and may commit (`pending >= batchLimit`, `:355`); `ForceCommit`
  (`backend.go:377`) is `lock`, `commit`, `Unlock` (`batch_tx.go:362-366`), and `commit` resets
  `pending = 0` (`:300`), so its `Unlock` writes nothing back (a hook the commit runs may write;
  `commit` still resets `pending`). The records change neither `pending` nor the commits (the loop
  writes no bucket). One token is stronger than what the proved `lessor.initAndRecover.spec` gives
  (`ownToks γB.wb 2`): the original's known margin, unchanged by records. So the part comes back idle with the bucket as it was
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
`lessorGuard`, the `Lookup` clause, `lessorCkptOk`), the configuration, the reader slots, `rd`
unset, `lessorBeOn`/`lessorApplyOk`, the stop right, is the original's, word for word: the loop
does not read the bucket, and every lease it sends or `Lookup` returns is the map's, with `GA` of
its id by the guard clause above.

**The empty bucket's clauses** (the statement until the Freeze; "the original" above), and why
each is true of the Go code: **`NewLessor(lg, b, cl, cfg)`** over the real backend `d` (`b` its `*backend`; D14d): the
lessor at `lp` (`lessorInv`, its configuration and `expiredC`, a reader slot of its lock for the
store, the live set empty, `SetCheckpointer` returns), and the contract of its backend for the
lessor's writes (`lessorBackend`), at the backend's batch lock `Pk` and any frozen post-lock hook
`f`, with one write-back token per write and the reader's open share lent (D14f). The `Lease`
bucket is in the backend's table, tracked, none of its keys a hook's (`mvcc.leaseParams d.P`, a
boot fact; 2026-11-01, E: so the bucket it creates is among the backend's ghost names `γ.rbD`, as
`rbOwnIn` of the result needs); a part of any bucket set `S` containing it comes back idle
(`rbPart d.γB S r` in, `rbOwnIn d.γB S (r.insert "lease" ∅)` out).

Why it is true of the Go code (`newLessor`, `initAndRecover`, `runLoop`, at the etcd pin):
* `newLessor` allocates the lessor (its maps, `expiredC` a channel of 16, `stopC`, `doneC`), sets
  the configuration's fields (a zero `leaseRevokeRate` defaulted to 1000: so a positive rate, given
  a non-negative one, `lessorCfg`; audit B4b, 2026-10-18), then `initAndRecover`:
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
  half of the field that the lock does not hold (`rdOwn γl func.nil`, unit T3).
* `go l.runLoop()`: until the lessor is promoted it only takes its lock, finds no expired lease
  and no due checkpoint; once promoted it sends expired leases on `expiredC` (the server's `run`
  receives them) and calls the checkpointer the server installed (`ckptEffectsOk`). **The grant
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
  (`lessorApplyOk`) is for whichever backend that is (its contract at some `W`, `Pk`, its frozen
  hook), given a write right lending that half of `le.b` (`rwLens`), which a write gives back (the
  lease-grant stage, 2026-11-02: the lent part `Ln`, apart from the spent token); `Recover`
  (names-only) replaces both halves under the lock. Until S7c `le.b` was `↦□` and the contract for
  `d` only, which `Recover` refutes.
* `Lookup(id)` (unit N4, D14h, 2026-10-17: `isApplyLessor`'s `Lookup` clause, a premise of
  `isApplyLessor_of_lessorInv` until then): it read-locks the lessor's `mu` and returns the map's
  lease or `nil`; a lease's `ID` is never written after `NewLease`, its `TTL()` and `Keys()` take the
  lease's own lock and return. The proved `lessor.Lookup.spec` takes a reader slot of `mu` (the
  model's `RWMutex` bounds its readers by the slots); the Go `RWMutex` panics only beyond `2 ^ 30`
  concurrent readers, which no etcd process reaches: the clause takes no slot. (The auth plan's
  E3zb, 2026-10-28) A lease it returns has the grant guard `GA` of its id: every lease of the map
  was granted (`lessorAuth`'s `leaseGranted`, kept by `Grant`, `Revoke` and `Recover`, which empties
  the map), and the lock's acquisition is the step that strips the guard's agreement's later (a
  server whose guard is `False`, `srvGrantGuard`, finds no lease: `lookupNil_of_guard`).
* The reader slots of `mu` (a `sync.RWMutex`, made by `newLessor`): one per reader (D14i,
  2026-10-17: the store's and the apply thread's lease owner each hold one).
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
  names (their fifth, `γr.2.2.2.2`), its whole authority in the readers' invariant, which keeps
  `reqOk` of the single empty snapshot and the empty map trivially (no lease, no TTL, no request).
  Allocatable because a fresh ghost map at `∅` is (`ghost_map_alloc`), before `γl`'s element pins
  the names. It makes no claim about Go: no Go state is read or written for it, and nothing about
  `NewLessor`'s code depends on it; `Grant` and `Recover` (proved) are what insert requests and keep
  every TTL above them.
* (2026-11-04, R2b-3c part 2, the user's approval) **The right to stop it** (`lessorStopTok lp`,
  for `lessor.Stop`): `newLessor` makes `stopC`, which only `Stop` closes; one right, given here. -/
abbrev lease.NewLessor.spec : Prop :=
  ∀ (lg : Loc) (cl : GoInterface) (cfg : go_etcd_io.etcd.server.v3.lease.LessorConfig)
    (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp) (GA : w64 → IProp GF)
    (S : GoString → Prop) (r : GMap GoString backend.BktData) (mono : Bool)
    (recs : List (w64 × w64 × w64)) (reqOf : w64 → w64) (Lr : List w64),
  S go!"lease" → mvcc.leaseParams d.P →
  backend.bktEnts ((r.lookup go!"lease").getD ∅) = recs.map lease.leaseRecEnc →
  (∀ x ∈ recs, sint.Z (reqOf x.1) ≤ sint.Z x.2.1) → Lr.Perm (recs.map (·.1)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ ⌜lg ≠ null⌝ ∗
      ⌜ckptEffectsOk⌝ ∗ ⌜0 ≤ sint.Z cfg.leaseRevokeRate'⌝ ∗ lease.clusterOk cl ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ backend.wbTok d.γB ∗
      backend.rbPart d.γB S r ∗ □ ([∗list] id ∈ recs.map (·.1), GA id) }}
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
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), lease.lessorRdOf γl) ∗
      lease.leaseOwn γl Lr ∅ ∗ lease.leaseEver γl (recs.map (·.1)) ∗ lease.leaseRevokers γl Lr ∗
      lease.rdOwn γl func.nil ∗ lessorCkptOk l ∗
      lease.lessorBeOn lp d.be ∗ lessorApplyOk lp ∗
      lease.lessorStopTok lp ∗
      □ ([∗list] x ∈ recs, lease.leaseReqIs γl x.1 (reqOf x.1)) ∗
      (∃ ls : List Loc, ⌜ls.length = recs.length⌝ ∗
        lease.lessorAt γl 0 (lease.recMap (recs.zip ls), ∅, lease.recTTLs cfg.MinLeaseTTL' recs)) ∗
      □ (∀ id : w64,
        {{ True }} (App (Val (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.lease.lessor.ty @!! go!"Lookup")) (Val #id))
        {{ (l : Loc), RET #l; ⌜l = null⌝ ∨ (apply.leaseIs l id ∗ □ GA id) }}) }}

end spec

end EtcdGrove
end Perennial
