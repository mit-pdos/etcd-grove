# Plan: the lease rows' key checks (spec-first; branch `lease-keys`)

Status (2026-10-31): **Scope decided** (the user's: Q1 (b) A then B, Q2 the lessor's item map, Q3
lower bounds; to follow the spec-first plan, `notes/spec-first-plan.md`). Part A's Draft in progress: items 1-4
done and proved (`ec422e5167`: the owner's `Lookup` opens its resource at the lease, the Probe);
item 5 deferred (it touches `UberOn`/`SnapRO`, other tracks' files); Q4 (the lease keys' length
bound, below) decided by the user, (b): `lease.itemKeysShort I` a conjunct of `leaseClosers`, kept
by `Attach` (a new premise) and `Detach`/`Revoke`, passed by mvcc's put path (`storeTxnWrite.put`/`Put`,
`metricsTxnWrite.Put`, `writeView.Put`: a premise on the key's length) from the request
(`txn.put`, `putRequestIs`); `leaseOwn_items_short` reads it. Q5 decided, (b): the lease class a separate conjunct of
`kvPost`/`kvPostF`. Items 6-12 drafted and proved; the Review done (below, "the Draft as
written"). Test: etcd's own tests of the checks pass. **Part A frozen** (the user's approval,
2026-10-31, at `97c2e6d92d`): a change to its statements now needs a `notes/decisions.md` entry with
its cause. Next: Part B. Started at
the user's request: the first of the three items that would let the repository answer
etcd-io/etcd#22595 ("Plan to revert Auth to Beta"), whose requirement "an audit to verify that RBAC
covers all etcd operations" `notes/auth-matrix.md` answers for every row but the lease keys.

## The gap

The matrix's rows that check **the keys a lease holds** are checked in Go but not stated:

| row | Go check | layer | translated |
|---|---|---|---|
| `Put` with a lease (also inside `Txn`) | `checkPutAuth` → `checkLeasePuts` → `checkLeasePutsKeys`: admin, or `IsPutPermitted` of every key of the lease | apply | yes, proved; `putClass` omits the lease's keys |
| `LeaseRevoke` | `authApplierV3.LeaseRevoke` → `checkLeasePuts` | apply | yes, proved; post states no class |
| `LeaseKeepAlive` | `EtcdServer.checkLeaseRenew`: admin, or `IsPutPermitted` of every key; then `ErrAuthOldRevision` if the auth revision moved | API | no (names only) |
| `LeaseTimeToLive` (`Keys = true`) | `checkLeaseTimeToLive`: admin, or `IsRangePermitted(k, "")` of every key; revision re-checked after the lookup | API | no |
| `LeaseLeases` | `checkLeaseLeases`: admin, or `IsRangePermitted(k, "")` of every key of every lease; revision re-checked | API | no |

GHSA-x35m-3gp4-4fh5 (a lease's keys not checked for a `Put` inside a transaction) is in this gap:
today's statements would not exclude it.

## What exists

- **The lessor has a key model, proved** (unit T3, L2b): `lease.Lease.Keys.spec` returns exactly
  the keys the item map `I` attaches to the lease (`k ∈ ks ↔ I.lookup ⟨k⟩ = some id`, no
  duplicates), for the holder of the lease owner's half `leaseItemsOwn l I id`, which
  `lease.leaseOwn γl L I` carries for every live lease.
- **At the apply thread the item map is the KV state's**: the contract's `Revoke` clause holds
  `lease.leaseOwn γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log))`. So an apply-layer
  statement over `I` is a statement over the keys the KV state attaches to the lease.
- **The apply package does not use it**: `apply.isApplyLessor`'s `Lookup` clause returns
  `leaseIs l id`, whose `Keys()` returns *some* keys (only their length bounded), and that clause is
  a premise of `isApplyLessor_of_lessorInv` (not proved of the real lessor). `checkLeasePutsKeys`
  takes no owner resource, so it cannot know which keys it checked.
- **No lease request is in the model**: `apply.rqOk`'s `leaseGrant` (and the other lease kinds) is
  `False`, and the contract's `Revoke` clause is vacuous. The matrix's statements are per method (a
  triple of the handler), so this does not block them; it means no closed theorem exercises them.

## Two parts

**Part A: the apply layer** (`Put` with a lease, `Txn`'s puts, `LeaseRevoke`).
1. `apply.leaseKeysClass M info I id`: auth off at a recorded state, or the principal admin at one,
   or for every key `k` with `I.lookup ⟨k⟩ = some id`, `classRes M info [(k, "", .write)]`
   (the shape `putClass` already uses).
2. The `Lookup` clause of `isApplyLessor` returns a lease whose `Keys()` meets `lease.Lease.Keys.spec`
   for the owner (`leaseOwnIs l id`: `isLeaseObj l` and the lease's `ID`), and is proved of the real
   lessor (`lease.lessor.Lookup.spec` is proved): one premise of `isApplyLessor_of_lessorInv` goes.
3. `checkLeasePutsKeys`, `checkLeasePuts`, `checkPutAuth` take the owner's `leaseOwn γ.leases L I`
   (framed back) and, on `nil`, give `leaseKeysClass` for the request's lease; `putClass` gains it
   (`TxnOp`'s puts too, which needs the lease in `TxnOp`); `authApplierV3.LeaseRevoke` states
   `leaseKeysClass` on success.
4. **Ripple: small (checked).** The auth layer already holds the owner's resource: every KV
   method's precondition has `mPre`'s `kvOwn E log`, whose `leasesLive` is `lease.lessorUser
   γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log))`, the owner's half at the KV state's item
   map. So `authApplierV3.Put`/`Txn`/`LeaseRevoke` lend it to the checks and take it back; no
   precondition of the chain changes. What changes is the class: `putClass` (and through it
   `reqClass`/`chainClass`) names the lease's keys, so it takes the log (`kvPost` has it), and the
   chain's layers above the auth applier pass the class through unchanged. These are definitions
   in `apply/AuthClass.lean` and `Chain.lean`'s `kvPost`, which the auth-mode merge
   (`notes/auth-mode-merge-plan.md`) may also touch: a merge to coordinate, not a dependency.

**Part B: the API layer** (`LeaseKeepAlive`, `LeaseTimeToLive`, `LeaseLeases`).
1. Translate `EtcdServer.checkLeaseRenew`, `checkLeaseTimeToLive`, `checkLeaseLeases` and the
   entry points `LeaseTimeToLive`, `LeaseLeases` (and `LeaseRenew`'s check call; `leaseTimeToLive`'s
   forwarding to the leader over `leasehttp` stays names-only, a contract).
2. These run on gRPC goroutines, not the lease owner: `Keys()` from a reader. The lessor needs a
   reader-side key model: the item set's history of each lease (or of the item map), so that a
   reader's `Keys()` returns the keys at some recorded point, and `Lookup`/`Leases` from a reader
   give live leases at some recorded point. A change to the lease package's invariant
   (`leaseItems`: today the owner's half and the lock's half of one set).
3. The class at recorded states, as the other API rows (`authPubLb`-style lower bounds): a
   successful check means each key, of a lease item set recorded no earlier than the check's start,
   was permitted at an auth state recorded no earlier than the check's start. The revision
   re-check (`ErrAuthOldRevision`) is what keeps the auth states' window to one revision; it
   becomes a clause of the spec.
4. Things to look at while drafting (possible findings): `LeaseTimeToLive` on a follower checks
   the follower's own lessor's keys, then asks the leader (`leaseTimeToLive` forwards over HTTP),
   so the keys checked and the keys returned come from different lessors; `checkLeaseTimeToLive`
   returns `0` with its error (unused by the caller).

## Questions for the user

- **Q1, scope.** (a) Part A only (the apply layer: the GHSA-x35m class; small, its ripple internal
  to the auth applier and the class definitions); (b) A then B (B is larger: a translation, the
  reader-side lessor history, three specs); (c) B first (the API layer and the lease package
  only). Recommended: (b), A first.
- **Q2, the key set.** The class over the lessor's item map `I` (what Go checks), which at the apply
  thread is the KV state's `leaseItemsOf` (so both readings agree there); at the API layer only the
  lessor's recorded item sets are available. Recommended: over `I`, with the apply-layer corollary
  over `leaseItemsOf`.
- **Q3, Part B's freshness.** As the other API rows: states recorded no earlier than the call's
  start (lower bounds), not the latest state. Recommended.

## Part A, Draft (the statements, top-down)

Found while drafting (Scope's survey refined):
- The txn package's lessor contract (`txn.isTxnLessor`) already has an owner-form `Lookup`: by the
  lease owner (`lease.lessorUser γl L I`), `nil` exactly when `id ∉ L`. It does not say the lease
  returned is the owner's lease of `id` (the closers' map element), which `Keys()` needs.
  The real `lessor.Lookup` can say it: under the read lock it reads the lease map `M`, whose
  ghost authority `γcl` (in `lessorMu`) agrees with the owner's closers' element.
- `apply.isApplyLessor`'s own `Lookup` clause (`leaseIs`: some keys, bounded) is redundant with
  `isTxnLessor`'s, and a premise of `isApplyLessor_of_lessorInv`. It goes.
- Txn's operations: `TxnOp.put k v lease`, `putKeep` (wire `Lease` 0), `putIgnVal k (lease : Option)`
  carry the lease, so `opClass` can name the lease's keys. Their `PrevKv` read is not in `TxnOp`
  (the other half of GHSA-x35m): **a related gap, not in this stage** (the model's put would need
  `prevKV`; recorded for after Part A).
- The keys' length bound (`IsPutPermitted` takes keys shorter than `2 ^ 63 - 1`): `leaseIs`'s
  `Keys()` assumed it. With the item map the KV state's (`leaseItemsOf`), it follows from the
  state's keys; to settle in Glue (a law over `leaseItemsOf`, or the key-length law).

The items (vocabulary first; each statement drafted in its file with its proof a `sorry` until
the glue):

1. `lease.leaseOwnOpen γl L I id l` (lease package, `InvLessor.lean`): the owner's resource
   `leaseOwn γl L I` opened at the live lease `l` of `id`: `isLeaseObj l`, the owner's half of its
   item set (`leaseItemsOwn l I id`) and its lock's reader slot, and the wand closing it back.
   Not persistent, on purpose: a revoked lease's object keeps its `ID`, and `id` can be granted
   again, so "the lease of `id`" holds only of the owner's current closers. Laws:
   `leaseOwnOpen_close` (back to `leaseOwn`), and the owner's `Keys()` over it
   (`lease.Lease.Keys.wp_open`, a corollary of `Lease.Keys.spec`: exactly the keys `I` attaches to
   `id`, no duplicates). `lessorUserOpen γl L I id l`, the same at the txn layer's `lessorUser`
   (`⌜l = null⌝ ∗ lessorUser γl L I`, or the reader slot, the revokers and `leaseOwnOpen`), with
   `lessorUserOpen_close`.
2. Law `lease.leaseOwn_items_live : leaseOwn γl L I ⊢ ⌜∀ it id, I.lookup it = some id → id ∈ L⌝`
   (`leaseClosers` has it): with `Lookup`'s `nil ↔ id ∉ L`, a `nil` lookup means no key has the lease.
3. `lease.lessor.Lookup.spec`: by the owner (`leaseOwn γl L I` in place of a share `leaseFrag γl q
   L`; every caller is the apply thread's, through `isTxnLessor`); post: `⌜l = null ↔ id ∉ L⌝` and
   `(⌜l = null⌝ ∗ leaseOwn γl L I) ∨ leaseOwnOpen γl L I id l`. (Part B adds the reader's form: an
   extension.)
4. `txn.isTxnLessor`'s `Lookup` clause: post `lease.lessorUserOpen γl L I id l ∗ ⌜l = null ↔ id ∉ L⌝`
   (for `lessorUser γl L I ∗ ⌜…⌝`); `txn.checkLease` closes it.
5. `apply.isApplyLessor`: the `Lookup` clause removed (callers use `isTxnLessor`'s); `leaseIs`
   removed if unused.
6. `apply.leaseKeysClass M info I id` (persistent; `AuthClass.lean`): in `on γa`, an admin at a
   recorded state (`adminOk`), or every key `k` with `I.lookup ⟨k⟩ = some id` write-permitted
   (`classOk γa info [(k, [], .write)]`); `True` otherwise.
7. `apply.checkLeasePutsKeys.spec`: pre `lease.leaseOwnOpen γ.leases L I id l` (for `leaseIs l id`),
   post it back and `err = nil → leaseKeysClass M info I id`.
8. `apply.checkLeasePuts.spec`: pre adds `lease.lessorUser γ.leases L I`; post adds the same class.
9. `apply.checkPutAuth.spec`: pre adds `lease.lessorUser γ.leases L I`; post's `putClass` gains `I`.
10. `apply.putClass M info I o := classRes M info (putPerms o) ∗ leaseKeysClass M info I o.leaseID`;
    `opClass`/`opsClass`/`txnClass` gain `I` (a put's lease: `lease`, `0` for `putKeep`,
    `lease.getD 0` for `putIgnVal`); `reqClass M info I rq` gains a `leaseRevoke` case
    (`leaseKeysClass` of its id); `chainClass` passes `I`; `kvPost` instantiates it at
    `mvcc.leaseItemsOf (mvcc.stateAfter log)` (the state before the request: Go checks before it
    applies anything).
11. `checkTxnReqsPermission`/`checkTxnPermission`/`CheckTxnAuth` specs (the transaction walk) take
    the owner's resource and give `txnClass` at `I`.
12. `authApplierV3.Put`/`Txn`/`LeaseRevoke` (and `UserGet`, which shares `kvPost`): statements
    unchanged but for `kvPost`'s class; their proofs lend `kvOwn`'s `lessorUser` to the checks.

Glue to prove before the freeze: 7 (`checkLeasePutsKeys`: the loop over `Keys()` with the class
accumulated), 8, 9 over 7-8, `authApplierV3.Put` over 9 (the lend from `kvOwn`), and 3 (the
`Lookup` agreement, a Probe: the one place the lessor's invariant is opened). Probe: also
`authApplierV3.LeaseRevoke` (the class for a request no workload admits yet).

### Draft finding: the keys' length bound (Q4, for the user)

`IsPutPermitted` (the auth store's real spec, `auth.authStore.IsPutPermitted.spec`, and the apply
contract `permCheck2`) takes a key shorter than `2 ^ 63 - 1` bytes. `checkLeasePutsKeys` passes each
of the lease's keys. Today that bound comes from `apply.leaseIs`'s `Keys()` clause, part of
`isApplyLessor`'s `Lookup` clause, which the server takes from `lease.NewLessor`'s **axiom** (its
post's `Lookup` triple, "true of every string in memory"). With the owner's `Keys()` (exactly the
item map's keys) nothing bounds them: neither the lessor's item map, nor mvcc's state, nor the
store's `put` (whose spec takes no key bound) carries one; only the request's own key has it
(`txn.putRequestIs`), and the server's KV invariant has the key-length law
(`EtcdModel.etcdState_keys`, `2 ^ 27`) above the apply layer. Options:
- (a) **the KV state's keys bounded at the apply thread**: a pure conjunct of `apply.leasesLive`
  (in `kvOwn`), kept by the backend layer's writes (each put's key has the bound from its request)
  and made at boot and at a snapshot's restore (the server's KV invariant's key-length law). Touches
  the chain's backend proofs, `NewServer`, the snapshot track's restore.
- (b) **the lessor's item map's keys bounded**: a pure conjunct of `lease.leaseClosers`, kept by
  `Attach` (a new premise: the items' keys bounded), whose caller, mvcc's `put` through
  `mvcc.isLessor`, gets it from a new premise of `storeTxnWrite.put` (and the txn layer's from the
  request); `Recover` from the backend's records. Touches the lease package and mvcc's write path.
- (c) **a named premise** of the lease-keys statements (`lease.itemKeysShort I`), carried in the
  chain's `putPre`/`txnPre`/`revokePre` and discharged at the server from the key-length law:
  every chain layer's precondition grows by one pure conjunct.
Recommended: (b): the bound travels with the key from the request that put it, in the package
that keeps the item map, and the server's other statements do not change.

**Decided (the user, 2026-10-31): (b).** No `Recover` change was needed: `store.restore` attaches
nothing (the restored `keyToLease` is empty).

### Draft finding: where the lease class lives (Q5, for the user)

Item 10 as drafted puts the lease class into `putClass`/`txnClass`/`reqClass` and so into
`chainClass`. Two consumers make that wrong:
- `txnClass` is also the read path's (`EtcdServer.Txn`, `doSerialize`, `ReadOn`, `ServerKVOn`: a
  read-only transaction checked at the server), which has no lessor owner and no item map. A
  read-only transaction has no put, so its lease class is `True`, but the definitions would need
  an `I` there. Hence the lease class is its own definition (`reqLeaseClass M info I rq`: a put's
  lease, every put of a transaction's two branches, a `LeaseRevoke`'s id), and `reqClass` stays.
- `chainClass` is also in the auth-on track's posts (`kvPostFL`, `AuthApplyLatest*`, through
  `UberKVLBase`/`DispatchKVL` to `ServerOn`), which are proved over `apply.lessorNil` (a lessor
  whose `Lookup` finds no lease: `checkLeasePuts` checks nothing). There the class holds only if
  the state has no lease items, which that track does not track (its `kvOwn`'s `L` is
  existential). The class in `chainClass` makes that track prove it.
Options:
- (a) **`chainClass` gains `I`**, its auth case `reqClass ∗ reqLeaseClass I`: the class through
  the whole chain and every result that states `chainClass`, including the auth-on server's. The
  auth-on track then needs "no lease items" (an invariant: no `LeaseGrant` reaches its model, so
  `L = []`), in its files (`AuthApplyLatest*`, `DispatchKVL`, `UberKVLBase`, `ServerOn`).
- (b) **a separate conjunct `chainLeaseClass E.authMode info I c rq oc` in `kvPost`/`kvPostF`**
  (not `kvPostFL`), with `I = mvcc.leaseItemsOf (mvcc.stateAfter log)`: the class through the
  chain's generic contract (`applierSpec`) to `Results.lean`'s `chain_put`/`chain_txn` (and a
  `LeaseRevoke` row if its method has `kvPost`); the auth-on track's statements and proofs do not
  change (its lessor finds no lease, and its posts say nothing of the lease's keys, as today). Every
  layer's KV-method proof that builds `kvPost`/`kvPostF` passes one persistent conjunct (backend:
  `True`; the wrappers: a lemma per layer, as `chainClass_quota`): mechanical, about 20 files of
  `apply/`.
- (c) **the method level only** (as `UserGet`'s `userGetClass`): `authApplierV3.Put`/`Txn`/
  `LeaseRevoke`'s own triples state it, the generic contract drops it. Smallest; the chain's
  results do not say it.
Recommended: (b): the class reaches the chain's results, as the matrix's other KV rows, without
touching the auth-on track; (a) can follow when that track models leases.

**Decided (the user, 2026-10-31): (b).** Items 6-12 as amended: `reqClass`/`putClass`/`txnClass`
unchanged; `reqLeaseClass` and `chainLeaseClass` new (`AuthClass.lean`, `Chain.lean`); `kvPost`/
`kvPostF` gain the conjunct; the auth layer's checks give `reqLeaseClass`.

### Part A, the Draft as written (2026-10-31, after Q4 and Q5, revised after the Review)

Drafted and proved (the build of `lease-keys`):
- `apply.leaseKeysClass M info I id` (`AuthClass.lean`): in `on γa`, an admin at a recorded state
  (`adminOk`), or `∀ k, I.lookup ⟨k⟩ = some id → classOk γa info [(k, [], .write)]`; `True` in the
  other modes. As every class, a permission at *some* recorded auth state (the review's F2); the
  latest-state track (`AuthApplyLatest.lean`, `kvPostFL`) states no lease class (Q5 (b)).
- `apply.opLeaseClass`/`opsLeaseClass`/`txnLeaseClass` (a put's lease, `putIgnVal`'s `some` lease,
  nested branches; `putKeep` and a lease-keeping `putIgnVal` are `True`: `TxnOp` forgets their wire
  `Lease`, the same gap as their `PrevKv`), `apply.reqLeaseClass M info I rq` (a put's
  `o.leaseID`, a transaction's, a revocation's id).
- **The lease view, only for the transaction walk** (`Contracts.lean`, `AuthClass.lean`):
  `CheckTxnAuth.spec` is also the server's read path's (`EtcdServer.Txn`), which holds no owner's
  resource; but that path walks only read-only transactions, which reach no put. So
  `checkTxnReqsPermission`/`checkTxnPermission`/`CheckTxnAuth` take `U : apply.LeaseView = Option
  (List w64 × GMap …)`: `apply.lessorView γl U` (`lessorUser γl L I`, or `True` for `none`) lent and
  given back, with the premise `⌜U = none → read-only⌝`, and give the classes under `apply.viewClass
  U C` (`C I`, or `True`). The read path instantiates `none`, the apply thread `some`. The put and
  lease checks take the owner's resource outright (the review's F3: the first draft had a `none`
  view there too, under which `checkLeasePutsKeys` stated nothing).
- `lease.leaseOwnOpen` starts with `⌜itemKeysShort I⌝` (the review's F6: the first draft paired it
  with `leaseOwnOpen` in a separate `leaseAtView`); `lease.lessorUser_items` reads it and the
  items' leases from `lessorUser`.
- Specs: `checkLeasePutsKeys` (`(γl L I)`, pre/post `leaseOwnOpen γl L I id l`; post
  `leaseKeysClass on info I id` on success; its proof takes `Lease.Keys.spec`, linked in
  `etc/link-lean-first-apply.txt`), `checkLeasePuts` (`lessorUser γ.leases L I` lent;
  `leaseKeysClass`), `checkPutAuth` (`putClass ∗ leaseKeysClass on info I o.leaseID`),
  `checkTxnReqsPermission` (`opsClass ∗ viewClass U (opsLeaseClass · ops)`),
  `checkTxnPermission`/`CheckTxnAuth` (`txnClass ∗ viewClass U (txnLeaseClass · t)`).
- `apply.chainLeaseClass M info I c rq oc` (`Chain.lean`, with `chainClass`'s lemmas mirrored), a
  conjunct of `kvPost`/`kvPostF` at `I = mvcc.leaseItemsOf (mvcc.stateAfter log)`; the auth
  applier's `Put`/`Txn` lend the owner's resource out of `kvOwn` (`kvOwn_lend`).
- `Results.lean`'s `chain_put`/`chain_txn` state `reqLeaseClass` beside `reqClass` for an outcome
  that passed the auth layer.

The Review (a spec-reviewer agent, 2026-10-31), its findings and what became of them:
- F1: `LeaseRevoke`'s lease class is vacuous: `rqOk` is `False` for a revocation, so no chain result
  reaches it. Documented (`reqLeaseClass`'s docstring); a revocation's result waits for the
  revocation track (the apply thread's `Revoke` clause, L3).
- F2: any recorded auth state, and no lease class on the latest-state track. Documented (above,
  `leaseKeysClass`).
- F3, F6: adopted (above).
- F4: `putKeep`/a lease-keeping `putIgnVal` could be covered through the wire model (`TxnModelW`,
  `rq.txnW`), as the `PrevKv` gap could. Deferred with the `PrevKv` gap.
- F5: `kvPostFL_kvPostF` (unused) no longer holds; deleted.
- F7: `chainLeaseClass` duplicates `chainClass`'s shape; a shared definition over the class would
  remove the mirrored lemmas. Low; recorded.
- F8: `AuthClass.lean`'s header, `putClass`'s and `opClass`'s docs said the lease keys were not
  stated. Fixed.
- F9: for Part B (the API layer), `Lookup.spec` must be generalized beyond the owner's resource
  (the API layer's checks run outside the apply thread).
- F10: a law relating the item map's keys to the KV state's keys would let a client read the class
  over the store's keys. Low; recorded.

Not yet: the lease class is not carried through `uberApplier.dispatch`/`Apply` (the dispatch drops
it); the server-level results state `reqClass` only. A follow-up.

## Part B, Scope (2026-10-31)

What exists: of the lease API, only `EtcdServer.LeaseGrant`, `LeaseRevoke` and `requireAuthInfo` are
translated (no spec of the first two); `checkLeaseRenew`, `checkLeaseTimeToLive`,
`checkLeaseLeases`, `LeaseTimeToLive`, `leaseTimeToLive`, `LeaseLeases`, `LeaseRenew` are names-only,
as are `lessor.Leases`, `lessor.Renew`, `Lease.Remaining`/`Demoted`. The lessor's `Lookup` and
`Lease.Keys` are specified for the lease owner only (the apply thread: `leaseOwn`); a gRPC goroutine
holds no owner's resource, and the lease's lock `l.mu` guards only the lock's half of the item set,
which says nothing of which lease it is or when. The server's reader resource pattern exists
(`RD`, the auth store's reader slots threaded through each call: `AuthReqDerive.lean`).

**B1. The lessor's reader-side key model** (the lease package's invariant). Recommended: a history
of the lessor's (lease map, item map), appended by the owner at each change (`Grant`, `Attach`,
`Detach`, `Revoke`, `Recover`), in a lessor invariant that also holds, for each `*Lease` ever
granted, a ghost variable of its item set, whose other part the lease's lock invariant holds. A
reader holding `l.mu`'s read lock then learns that `l.Keys()` is the item set of `l`'s id at a
recorded index no earlier than its lower bound: the current index while `l` is live, the index of
its revocation after (Go's `Revoke` does not clear `l.itemSet`, and `id` can be granted again, so a
revoked lease's set is pinned to its revocation's index, which is after any `Lookup` that found
it). `Lookup`/`Leases` from a reader (the lessor's read lock) give leases live at an index no earlier
than the lower bound. This touches every lessor method that changes the maps and the lease
package's interface (`InvLessor`'s owner resources, `Lookup.spec` generalized: review F9).

**B2. The specs.** Lower bounds (Q3): a passed check means, of every key of the lease's item set at
a lessor index `≥ n0` (the caller's lower bound at the call), the principal's `IsRangePermitted`
(`TimeToLive`, `Leases`) or `IsPutPermitted` (`Renew`) at a recorded auth state, or the
principal an admin at one; and the revision re-check (`ErrAuthOldRevision`) states the auth states'
window. `checkLeaseLeases` over the leases `Leases()` returned.

**B3. Finding: `LeaseTimeToLive` returns keys it did not check** (reproduced with gofail, on the
leader and a follower: `issues/etcd-lease-timetolive-keys-toctou.md`). `checkLeaseTimeToLive` checks the keys of the local
lessor's lease; `leaseTimeToLive` then looks the lease up again (on the leader) or asks the leader
(on a follower) and returns that lease's keys. A key attached in between (by a user who may write
the lease's earlier keys: `checkLeasePuts`) is returned to a principal who may not read it; the
revision re-check catches only auth changes. So `LeaseTimeToLive`'s spec can state the class of the
keys it checked, not of the keys it returns.

**B4. The extent of the translation.** `LeaseRenew` (the KeepAlive row) and `leaseTimeToLive` carry
much besides the check: leadership (`isLeader`, `ensureLeadership`, `waitLeader`), the applied
index's wait, the forwarding over `leasehttp` (names-only, a contract), the `FastLeaseKeepAlive`
feature, `lessor.Renew` (the expiry heap, `refresh`, the checkpointer), a timed retry loop.

**The user's decisions (2026-10-31).** B4: **the three checks only** (`checkLeaseRenew`,
`checkLeaseTimeToLive`, `checkLeaseLeases`, with `lessor.Leases` and `Lease.Keys` from a reader);
the entry points stay names-only, so no lease row is closed at the handler level, and B3 does not
reach a spec. B1: **the history, with lower bounds**, as recommended.

## Part B, Draft (the design, top-down; 2026-10-31)

**The checks' specs** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__checkLease*.lean`,
vocabulary in `Proof/.../etcdserver/LeaseCheck.lean`), each for a caller with the auth store's
reader resource `RD` and a lower bound `n` of the published auth index (`auth.authPubLbM`, as
`CheckTxnAuth.specLb`), a reader slot of the lessor's lock (`lease.lessorRdOf γl`), its thread token
(`threadTok`, under `threadBound GF ≤ 2^30 - 1`: `Keys()` borrows a slot of the lease's lock from the
lease's thread pool) and a lower bound `m` of the lessor's history (`lease.lessorLb γl m`); on `nil`
(`leaseCheckFrom`): auth disabled at a state `≥ n`, or the principal an admin at one, or the keys'
verdicts:
- `checkLeaseTimeToLive(ctx, id)` (`leaseKeysVerdictFrom … .read`): no lease of `id` at a lessor
  index `≥ m` (`leaseAbsentFrom`), or its lease `l` there with keys `ks` (`leaseKeysFrom γl m id l
  ks`), `IsRangePermitted(k, [])` passed at a state `≥ n` for each (`auth.permVerdictFrom`); and the
  returned revision the auth store's at a state `≥ n` (`auth.revisionVerdictFrom`).
- `checkLeaseRenew(ctx, id)`: the same with `IsPutPermitted` (`.write`).
- `checkLeaseLeases(ctx, leases)`: over the slice of `(l, id)` pairs (each `l` the lease of `id` at
  an index `≥ m`: `leaseLiveFrom`), each lease's keys as above with `IsRangePermitted`
  (`leaseOfKeysVerdictFrom`).
- **The margin**: the revision re-check (`ErrAuthOldRevision` unless `Revision()` is unchanged
  across the keys' checks) is not stated: the verdicts say each check's state is `≥ n`, not its
  revision, so stating it needs verdicts at a revision (`checkLeaseRenew.spec`'s docstring).

**The lessor from a reader** (the lease package, `InvLessor.lean`):
- The lessor's history (`γr.1`, in the pin): a monotone list of `(M, I)` snapshots (lease map, item
  map), appended by the owner at each change under `le.mu`'s write lock; `lessorLb γl m`
  (persistent) a lower bound of its length. An invariant (`lessorRdInv`) holds a quarter of the
  list's authority and half of the item-sets map's (`γr.2`: every `*Lease` ever in the history to
  its item set; the other half in `l.mu`'s invariant, `leaseItems`), equal to the item set of `l`'s
  id at the last index where the lease map has `l` (the current one while `l` is live; frozen at its
  revocation, since Go's `Revoke` does not clear `l.itemSet` and the id can be granted again).
- `lease.leaseLiveFrom γl m id l` (persistent): `l` is the lease of `id` at an index `≥ m`;
  `lease.leaseAbsentFrom γl m id`: `id` is not live at one; `leaseKeysFrom γl m id l ks`: `ks` are
  `id`'s keys at an index `≥ m` where the lease map has `l`.
- The leases' reader slots: `isLeaseObj γl l` holds a thread pool (Perennial's `threadPool`) of
  `l.mu`'s slots under `threadBound GF ≤ 2^30 - 1` (as logkvrw), so a reader with its thread token
  borrows a slot for one `Keys()` and gives it back.
- **One spec per function** (the Review's finding 3): `lessor.Lookup.spec` takes a lower bound and
  an optional owner's view (`lookupView`: none for a reader, the owner's `leaseOwn` otherwise) and
  returns `nil` and `leaseAbsentFrom`, or `isLeaseObj l` and `leaseLiveFrom`, plus the owner's facts
  (`lookupViewAfter`); `Lease.Keys.spec` takes who reads (`KeysBy`: the owner with its half of the
  set and a slot, or a reader with `leaseLiveFrom`, its thread token) and returns the keys as the
  owner's item map has them or as `leaseKeysFrom`.
- What changes for the owner: `Grant`, `Attach`, `Detach`, `Revoke`, `Recover` (and `NewLessor`,
  `NewLease`) append to the history / allocate the ghost state and the lease's pool. The owner's
  specs' statements stay (the definitions they are written in grow), but for `Lookup` and `Keys`,
  each now one spec for both callers.

`checkLeaseLeases` takes its slice as a premise (each lease `leaseLiveFrom`); `lessor.Leases` waits
for the entry points: it sorts with `sort.Sort(leasesByExpiry(ls))`, whose `Less` compares
`Remaining()`, which reads the clock (and `expiry`, which `Renew` moves), so it is no fixed order,
and Perennial's `sort.Sort.spec` needs `Less` to agree with a strict weak order. A spec of `Sort`
for any `Less` (a permutation, no order) would be a Perennial change (recorded in
`notes/perennial-changes.md` when the entry points are taken up).

**Not in Part B** (the user's B4): the entry points and their server-level resources (the request
slots' `lessorRdOf` and thread tokens, the lessor lower bound at a handler's start), and the auth side's
`IsAdminPermitted` at a lower bound (`specLb`; an additive lemma in the auth package, to check
with the auth work in progress).

**Draft finding: the trust boundary (for the user, 2026-10-31).** The reader-side model is ghost
state that the lessor's invariant and the owner's resource carry; two of the lessor's results that
build or rebuild them are axioms: `lease.NewLessor.wp_proof` (names-only constructor) and
`lease.lessor.Recover.wp_proof` (names-only). Their statements' text would not change, but the
definitions they are written in (`lessorInv`, `leaseOwn`, `leaseRevokers`) would, so what they
assert grows: `NewLessor` allocates the history at the empty maps (`[(∅, ∅)]`) and the item-sets
map empty; `Recover` appends the fresh empty maps to the history (every
lease of before revoked there, its item set frozen at its last live index, as `Revoke` does). The
docstrings' arguments extend directly (fresh ghost state, a ghost update under the lock), but it
is a trust-base change: the user's gate. `Promote`/`Demote`/`scheduleCheckpointIfNeeded` (axioms)
do not touch the two maps. The pin gains the reader names (`LessorGV`'s first component), inside
`lessorPinG` (its arity unchanged).
**The user's decision (2026-10-31): approved**, with an axiom review (the `axiom` skill) of the
restated `NewLessor`/`Recover` before the freeze.

**The Draft's definitions** (`InvLessor.lean`):
- The pin's first component gains `γr : LessorRdNames` (the history `γr.1`, a monotone list of
  `LSnap = (lease map, item map)`; the item sets' ghost map `γr.2`, `*Lease` to its item set).
- `leaseItems γl l q` (`l.mu`'s invariant) gains the item sets' map element of `l` at `q`; so
  `isLeaseObj γl l` takes the lessor's name, and holds `lessorRdInv` and the lease's thread pool.
- `lessorRdInv γl` (an Iris invariant, in `lessorInv`): a quarter of the history's authority, half
  of the item sets' map's authority, `setsOk` (each `*Lease`'s set is its id's items at the last
  index the lease map has it, or empty if it never had it), `histOk` (nonempty, each lease under one
  id, every snapshot's keys short), and each `*Lease` of the map's `ID ↦□` (`Grant`'s freshness).
- `lessorMu` gains a quarter of the history's authority per unit of the lock's fraction, its last
  snapshot the lock's maps; `leaseClosers` the owner's half of the history's and of the item sets'
  authority, the last snapshot the owner's maps.
- Readers' vocabulary: `lessorAt γl i σ`, `lessorLb γl m` (a prefix lower bound), `leaseLiveFrom
  γl m id l`, `leaseAbsentFrom γl m id`, `leaseKeysFrom γl m id l ks`; laws `lessorLb_le`,
  `lessorLb_get`, `leaseLiveFrom_lb`, `leaseKeysFrom_short`, `leaseOwn_lb`.
- `lease/Reader.lean` (the Draft's reader-only specs) is gone, into the unified specs.

**The Review** (2026-10-31, an independent `spec-reviewer`): (1a) `lessorReader` could not be
obtained and (1b) `Keys` from a reader could not show its lease in the item-sets map: both fixed by
the thread pool in `isLeaseObj` (no custom pool, no membership needed); `Grant`'s freshness: the
invariant keeps each lease's `ID ↦□`; `lessorLb` made a prefix bound with its laws; one spec per
function (`Lookup`, `Keys`); TimeToLive's returned revision stated; `checkLeaseLeases` ties each
lease to its id; the revision re-check named as the margin; docstrings of `lessorMu`,
`leaseClosers`, `NewLessor`, `Recover` extended. Left as recorded: `IsAdminPermitted` at a lower
bound unproved (Not in Part B); `srvAuthLeaseLb` separate from `srvAuthLb` (it adds the lease
checks' methods `IsAdminPermitted`/`IsPutPermitted`, which no read-path check needs).

**The axiom review** (2026-10-31, the `axiom` skill on the restated `NewLessor`/`Recover`, branch
`axiom/lessor-reader`, `881a927f93`, report `notes/axiom-review/lessor-reader.md` there): **survives**
(eight attacks: two history authorities, keys a lease never had, item sets after `Recover` (a Go
test at the pin), `setsOk`'s new conjunct, more readers than the lock allows, unallocatable ghost
state, a client forging lease state, `Recover` racing readers). Collections resting on the two
axioms: authkv, linkvtxn, cachekv, linkv3p, server, putget, k8setcd3, putget3, watchkv.

**The Probe** (2026-10-31): `Lease.Keys.wp_proof` re-proved for both callers (`itemSet_keysFrom`:
under the read lock, the reader's element of the item sets' map is its id's items at the last
index the lease map has `l`, `≥ m`); `itemSet_register`, `Grant`'s step that registers a fresh
`*Lease` with the empty set. It found two Draft errors, fixed: `setsOk` must also say every lease
of the history has a set (else a fresh `l` could not be shown absent from the history), and the
pool's premise is `threadBound GF ≤ 2^30 - 1` (`actualMaxReaders = 2^30 - 1`, less the owner's slot;
the axiom review found it too). A Perennial gap worked around locally: a typed points-to's fraction
validity (`w64_own_discard_false`; `notes/perennial-changes.md`). The `Lookup` reader case needs no
invariant opening (`lessorMu`'s share of the history has the last snapshot, the lower bound is a
prefix of it).

**Test** (2026-10-31): etcd's own tests of the lease checks pass at the pin (go1.27.3):
`tests/integration` `TestV3AuthWithLease*`, `TestPutWithLeaseInTXN`; `tests/common` (`-tags
integration`) `TestAuthLease*`. The TOCTOU the checks' specs leave as their gap is reproduced in
`issues/etcd-lease-timetolive-keys-toctou.md`.

**Part B frozen** (the user's approval, 2026-10-31, at `211662f7ba`): the three checks' specs, the
unified `Lookup`/`Keys` specs, the readers' vocabulary (`InvLessor.lean`), the restated
`NewLessor`/`Recover`. A change to them now needs a `notes/decisions.md` entry with its cause.
Next: Prove.
