# LeaseRevoke through the apply chain (spec-first)

Item 1 of the lessor/auth interaction (2026-10-31, the user: "start with 1, spec-first"): a
`LeaseRevokeRequest` through the apply chain, so that the auth layer's check of the lease's keys
(`authApplierV3.LeaseRevoke`: `checkLeasePutsKeys`, every key attached to the lease writable by the
principal) is a proved fact about a revocation the chain really performs, not about a request the
workload excludes (`rqOk .leaseRevoke = False`, D14h).

Branch `lease-revoke`, worktree `/shared/etcd-grove-leaserevoke` (off `lease-keys` `bf7efdb4ac`,
`lean` merged).

## Scope (decided 2026-10-31: "Apply chain")

In:

- `isApplyLessor`'s `Revoke` clause made real (no `⌜False⌝`) and derived of the proved
  `lessor.Revoke` (`apply.isApplyLessor_of_lessorInv`);
- `rqOk` admitting a revocation (its premise: room for one more revision, and the state bound
  `lessor.Revoke` takes);
- `chain_revoke` in `apply/Results.lean`, as `chain_put`: the outcome, the answer, the KV and the
  chain's resources after, and `∀ _ : authPassed oc, reqClass ∗ reqLeaseClass` (the latter is
  `leaseKeysClass` of the item map before);
- the ripple through the proofs that eliminated the case by `rqOk = False` (the backend's
  `LeaseRevoke`, the wrappers, dispatch).

Out: the server's `plainCover` and its rest model, and the entry point `EtcdServer.LeaseRevoke`
(T3's L3c/L4, `notes/leases-plan.md`); grants (`rqOk .leaseGrant` stays `False`).

## What the Draft found (2026-10-31)

`lessor.Revoke.spec` (proved) takes more than the clause names. The apply thread holds most of it:

| `lessor.Revoke` takes | the apply thread's source |
|---|---|
| `watchWriter γw log` | `kvWriter`'s `soleWriter` + `wlogOwn` (a watchable store: `soleBudget = wBudget`, as `txn.kv_Write` does) |
| `hookIs γ P f` | `hookOk` (persistent, the environment's) + `kvWriter`'s `writerFrag` |
| `storeReader`, `storeWT`, `certOkNext` of deletes | `kvOwn`, the clause's premises |
| `leaseOwn`, `leaseRevokers` | `leasesLive`'s `lessorUser` |
| `log.length + 4 ≤ 2^63`, `(stateAfter log).length ≤ 2^62` | `soleWriter_small` (and a lemma: the state no longer than the log's changes) |
| `storeRb γ r`, `lessorBeOn lp be` | **not lendable through `E.RW`**: the server's `RW` is the tracked buckets' client half, which the apply thread holds in `E.RO` and never lends |
| `rdOwn γl rd`, `rdIs rd ws st γw` | **not held**: the server's build gets them (`BuildLemmas`, `∃ rd, rdOwn ∗ rdIs`) and drops them |

### F1: the bucket write goes through `E.RO`, as the cluster's

A revocation deletes the lease's record from the `lease` bucket (`restRevoke`, `apply/RestLease.lean`,
already stated for L3c). The cluster's writers (`isCluster`'s `SetVersion`) take `RO r` and give
`RO (eff r)`; the Revoke clause does the same: `RO r` before, `RO (restRevoke id r)` after a
revocation of a live lease, `RO r` otherwise. The server's `RO` lends `rbOwn` (= `storeRb` of its real
backend) and the lessor's `lessorBeOn` (`srvObjsOn`). The server's rest *model* (`restModel`, a
function of the log) does not yet know which revocations hit a live lease: that is L3c, out of scope.
`chain_revoke` states the effect on `E.RO`; the server meets it when L3c lands.

### F2: the range deleter's owner, and a false claim of `lessor.Recover`'s axiom

`Revoke` reads `le.rd` outside the lock by the owner's half (`rdOwn γl rd`), and calls it at the
watchable store (`rdIs`). The apply thread does not hold either. Worse, a snapshot's apply calls
`s.lessor.Recover(newbe, func() lease.TxnDelete { return s.KV().Write(traceutil.TODO()) })`, and Go's
`Recover` stores that closure (`le.rd = rd`, `lessor.go:605`), but `lease.lessor.Recover.spec` neither
takes `rdOwn` nor returns it: `lessorMu`'s half of `le.rd` and `rdOwn`'s pin the field at the old
value, so after the axiom the logic says `le.rd` is the old closure while Go holds the new one. A
program that `Recover`s with a panicking `rd` and then revokes a granted lease panics in Go; the logic
would call the old closure. (Not exploited by the server, whose two closures both call the same
watchable store's `Write`; no Lean counterexample built.) The true statement: `Recover` takes
`rdOwn γl rd0` and returns `rdOwn γl rd`, as `SetRangeDeleter` does. Recorded in
`notes/audit.md`; restating the axiom needs the user's approval.

### Options for F2 (the user's decision)

- **(a) premise:** the clause and `chain_revoke` take `∃ rd, rdOwn γl rd ∗ rdIs rd ws st γw` from
  their caller (a resource beside `kvOwn`, returned). Stays inside the apply chain; the server's
  apply thread and the snapshot path get it with L3c, along with the `Recover` fix.
- **(b) in `kvOwn`:** add it to the apply thread's KV resources now; restate `Recover` (trusted);
  re-establish `rdIs` after a snapshot's `Restore` (new names) and for `applySnapshot`'s closure.
  Reaches into the server's snapshot path (out of the chosen scope).

F2 decided 2026-10-31: **(a) premise**. The `Recover` row stays **false** in `notes/audit.md`
until L3c restates it.

### F3: in the server's workload no lease is ever live

`rqOk .leaseGrant` stays `False`, and `Recover` reloads only the image's leases, of which the workload
has none (Go's `Recover` reloads every lease of the new backend's bucket), so at the server every
revocation finds no lease (`ErrLeaseNotFound`). The apply chain's statements are generic over the
live set (`leasesLive`'s `∃ L`), so `chain_revoke` must still cover a live lease; what it proves
of the server today is the error path, and of an apply chain with grants the deletion.

## Draft

**D1. The revocation's outcome, exact** (`apply/Chain.lean`). Today `backendStep`'s case is loose
(some deletions). It becomes a function of the state, as T2 made the put's, the delete's and the
transaction's:

```lean
/-- **A revocation's deletions** at the state `s`: every key the item map puts on `id`
(`leaseItemsOf`: a key with lease `0` has none), in the state's (key) order. -/
def revokeDels (s : List EtcdKv) (id : w64) : List mvcc.Change :=
  if id = W64 0 then [] else (s.filter (fun v => v.lease = id)).map fun v => .del v.key

  | .leaseRevoke => ∃ id, rq.leaseRevoke = some id ∧
      o = .applied (mvcc.commitLog log (revokeDels (mvcc.stateAfter log) id)) false
```

A lease that is not live has no key (`leaseClosers`: every lease of the item map is live), so its
deletions are `[]` and the log stays; the answer's error (`revokeOutcomeIs`, unchanged) is the
lessor's. `KVModelDefs.revokeChanges` (the server's model, L3a, guarded by `id ∈ lt.ids`, never
`0`) equals it there (a lemma, `revokeChanges_eq`).

**D2. The premise** (`rqOk .leaseRevoke`): `putOk log` (room for one revision). `lessor.Revoke`'s
second bound, `(stateAfter log).length ≤ 2^62`, is derived: the state is no longer than the log's
changes (`stateAfter_length_le`, new, in `mvcc/LogLemmas.lean`) and the sole writer's log has fewer
than `2^48` (`soleWriter_small'`).

**D3. The Revoke clause** (`apply/Contracts.lean`, `isApplyLessor`). `isApplyLessor` gains the rest
resource `RO : RestM → IProp GF` (as `isCluster`). With `log`, the live set `L`, the range deleter
`rd` at the watchable store `ws` over `s` (names `γw`, `γw.st = γ`), the rest model `rs`:

```lean
{{ mvcc.csContract P f Pre Q Post ∗ txn.kvWriter s γ log ∗ mvcc.storeReader s γ ∗ mvcc.storeWT γ ∗
    ⌜putOk log⌝ ∗
    lease.leaseOwn γ.leases L (leaseItemsOf (stateAfter log)) ∗ lease.leaseRevokers γ.leases L ∗
    txn.leasesKnown L (stateAfter log) ∗
    lease.rdOwn γ.leases rd ∗ mvcc.rdIs rd ws s γw ∗ ⌜γw.st = γ⌝ ∗ RO rs ∗
    (□ ∀ pend, ⌜∀ c ∈ pend, c.isDel⌝ -∗ mvcc.certOkNext γ log pend) }}
  Revoke id
{{ err; mvcc.storeReader s γ ∗ lease.rdOwn γ.leases rd ∗ applyErrIs err ∗
    let log' := commitLog log (revokeDels (stateAfter log) id)
    ((⌜id ∉ L ∧ log' = log⌝ ∗ Pre ∗ mvcc.storeWT γ ∗ txn.kvWriter s γ log ∗
        leaseOwn L … ∗ leaseRevokers L ∗ leasesKnown L … ∗ RO rs) ∨
     (⌜id ∈ L ∧ err = nil⌝ ∗ Post ∗ txn.kvWriter s γ log' ∗
        leaseOwn (L.filter (· != id)) (leaseItemsOf (stateAfter log')) ∗
        leaseRevokers (L.filter (· != id)) ∗ leasesKnown (L.filter (· != id)) (stateAfter log') ∗
        RO (restRevoke id rs))) }}
```

Derived in `isApplyLessor_of_lessorInv` from `lessor.Revoke.spec`, with new premises of the
derivation (what `NewServer` supplies): the store is watchable (`γ.watchQ`, so `kvWriter` is
`watchWriter`'s tokens, certificate and half log), the hook's facts `hookOk γ P f`, and a lens
`□ ∀ rs, RO rs -∗ ∃ d, ⌜γ.kb = some d⌝ ∗ mvcc.storeRb γ rs.bk ∗ lease.lessorBeOn lp d.be ∗ (∀ bk,
storeRb γ bk ∗ lessorBeOn lp d.be -∗ RO {rs with bk})`. `lessor.Revoke`'s `ks` (sorted, no
duplicates, exactly the keys the item map puts on `id`) is `revokeDels`'s keys: two sorted lists
without duplicates and with the same members are equal (`stateAfter_sorted`).

**D4. The method's premise and result** (`revokePre`, the applier's LeaseRevoke triple):
`revokePre` gains `revokeRes E rs := (∃ rd ws γw, lease.rdOwn E.γ.leases rd ∗ mvcc.rdIs rd ws E.s
γw ∗ ⌜γw.st = E.γ⌝) ∗ E.RO rs`, and the triple's post gives back the range deleter and
`E.RO rs'` with `rs' = restRevoke id rs` or `rs` (`∃`, with `err = nil` in the first: the apply
layer does not know the live set; the server's model does, L3c).

**D5. `chain_revoke`** (`apply/Results.lean`), as `chain_put`:

```lean
theorem chain_revoke (E : AEnv GF) (ns cr : Bool) (a : GoInterface) :
    applierSpec E (alarmChain E.authOn ns cr) a ⊢
      ∃ ai : GoInterfaceOk, ⌜a = GoInterface.ok ai⌝ ∗
      □ (∀ r rq id log rs Pre Q Post info,
        {{ revokePre E (alarmChain E.authOn ns cr) (.ok ai) info r rq id log rs Pre Q Post }}
          (App (Val #(methods ai.ty go!"LeaseRevoke" ai.v)) (Val #r))
        {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
            ∃ oc, ⌜alarmRevoke ns cr id log oc⌝ ∗ revokeOutcomeIs resp err oc ∗
              kvOwn E (oc.logAfter log) ∗ chainRes … info ∗ (Post ∨ Pre) ∗ revokeResAfter E id rs err ∗
              (∀ _ : authPassed oc, reqClass E.authMode info rq ∗
                reqLeaseClass E.authMode info (leaseItemsOf (stateAfter log)) rq) }})
```

`alarmRevoke ns cr id log oc`: the backend's `applied (commitLog log (revokeDels …))`, or the
chain's rejections (auth, no space, corrupt) as `alarmPut`. `reqLeaseClass .leaseRevoke` is
`leaseKeysClass` at `id`: in the mode `on`, the principal is an admin or may write every key the
lease holds before the revocation (what `authApplierV3.LeaseRevoke`'s `checkLeasePutsKeys` checks).

**D6. The ripple.** `applierV3backend.LeaseRevoke` (vacuous today) proved from D3; the wrappers
(`authApplierV3`, `applierV3Corrupt`, capped and quota pass it on) carry `revokeRes`;
`isApplyLessor`'s new `RO` argument through `applierSpec`/`opts` and `NewServer`'s derivation (its
new premises: watchable store, `hookOk`, the RO lens over `srvRestOwnH`). `uberApplier.dispatch` is
unchanged: its KV path excludes the kind by its own premise (`isKVKind`, `DispatchKVL.lean`), and
the server's `plainCover` keeps excluding it. `KVModelDefs`'s proofs that matched `backendStep`'s old
case are re-checked.

## Review (2026-10-31, `notes/spec-review/lease-revoke-draft.md`) and the Draft revised

The independent review's findings, and what each changes (R = revision):

- **D3-1 (blocker)**: `lessor.Revoke.spec` asks `□ ∀ pend` (any deletions) `certOkNext`; with D1
  exact, `certPre` certifies only the one log, so the clause cannot be supplied (and at the server the
  `∀` is false). **R1**: restate the proved `lessor.Revoke.spec` at its actual deletions,
  `mvcc.leaseDels (stateAfter log) id` (D1's `revokeDels`, moved to mvcc and shared), its premise
  `certOkNext γ log (leaseDels …)` and its post `watchWriter` at `commitLog log (leaseDels …)` in
  place of `∃ ks`; the sorted-list equality (`ks` = `leaseDels`'s keys) moves into its proof. A change
  to a proved statement: **the user's approval**, a `notes/decisions.md` entry.
- **D3-2/D4-2 (blocker)**: `rdIs` at fixed names `γw` cannot meet `kvWriter`'s hidden ones (only the
  locations are unique). **R2**: the range deleter's resource is
  `lease.rdAt γl s := ∃ rd, rdOwn γl rd ∗ □ ∀ ws γw, isWatchableStore ws s γw -∗ rdIs rd ws s γw`
  (one name, in the lessor's API: D4-3), as `txn.kv_Write` takes `Write`.
- **D2/D6 (major)**: `rqOk`'s case also excludes revocations in `uberApplier.dispatch` and the
  server's `KVApply`. **R3**: `rqOk .leaseRevoke` stays `False`; `revokePre` takes `putOk log` in its
  place (its `rqOk log rq` conjunct goes).
- **D5-1 (major)**: the capped and quota appliers do not override `LeaseRevoke`: no `noSpace`
  rejection. **R4**: `revokeChain c id log oc`: corrupt (if `cr`) or auth-rejected or the backend's.
- **D5-2 (major)**: with auth off `checkLeasePutsKeys` returns `nil`. **R5**: `.leaseRevoke` joins the
  kinds the auth layer rejects only when on (`authMayReject`).
- **D4-1/D3-3 (major)**: the RO effect as `∃` is unusable, and Go is deterministic. **R6**:
  `E.RO (if err = nil then restRevoke id rs else rs)`, the not-found branch with `err ≠ nil`
  (`ErrLeaseNotFound`'s `lessorErrIs`). Telling "not found" from "live with no keys" stays the server's
  (L3c: the live set).
- **D5-3**: **R7**: `revokeOutcomeIs`'s applied case states the response (not nil, its header at the
  revision after).
- **D1-2/D5-4**: **R8**: a law `leaseDels_mem` (a deleted key is one the item map put on `id`).
- **D1-1**: `revokeChanges_eq`'s premises spelled out (every non-zero lease of the state in
  `lt.ids`, `0 ∉ lt.ids`). **D3-4**: the lens is `roLens`. **D4-4**: the docstring says the write
  token is spent even with no deletion.

## The Draft in code (2026-10-31)

- R1 done: `mvcc.leaseDelKeys`/`leaseDels` with `leaseDelKeys_mem`, `leaseDels_mem`,
  `leaseDels_isDel`, `leaseDelKeys_sorted`, `leaseDelKeys_eq` (`mvcc/LeaseItems.lean`);
  `lease.lessor.Revoke.spec` restated, its proof re-run (`lake build`: green); `notes/decisions.md`,
  "`lessor.Revoke` at its actual deletions".
- The apply side's statements: `apply/LeaseRevokeDraft.lean` (`revokeStep`, `authMayRejectR`,
  `rdAt`, `revokeClause`, `revokeRes`/`revokeResAfter`, `revokePreR`, `revokeOutcomeIsR`,
  `chainRevokeStmt`, `deriveRevokeStmt`), beside `Chain.lean`'s until Prove. R4 needs no new model:
  `chainStep`'s capped layer rejects only puts and grants (`cappedRejects`). R7: `newHeader`'s spec
  gives only a non-nil header, so the answer says `resp ≠ null` (the header's revision is the server's,
  out of scope).

## Test (2026-10-31)

etcd's own tests of revocation pass at the pin (go1.27.3):
- `server/etcdserver/apply`: `TestAuthApplierV3_LeaseRevoke` (a user may revoke a lease with no key
  outside its range, not after root attaches one: `chainRevokeStmt`'s `leaseKeysClass`),
  `TestCheckLeasePutsKeys`, `TestAuthApplierV3_AdminPermission` (a revocation needs no admin
  permission), `TestUberApplier_Alarm_Corrupt` (a revocation's `ErrCorrupt`);
- `tests/integration`: `TestV3AuthWithLeaseRevoke{,WithRoot,WithRootJWT}`, `TestV3LeaseRevoke`,
  `TestV3LeaseRecoverAndRevoke`, `TestV3LeaseRevokeAndRecover`;
- `tests/common` (`-tags integration`): `TestAuthLeaseRevoke`, `TestLeaseGrantRevoke`.

F2 in Go: a test in `server/lease` (`SetRangeDeleter` to a no-op deleter, `Recover(be2, func()
TxnDelete { panic(...) })`, `Grant(1, 100)`, `Revoke(1)`) panics with `Recover`'s deleter: `Revoke`
calls the deleter `Recover` stored, not the one the model's `rdOwn` still names (run 2026-10-31, not
kept in the tree).

## Probe (2026-10-31)

`apply/LeaseRevokeProbe.lean` (no `sorry`): `kvWriter_open` (R2: the KV's writer opens to
`watchWriter` at the names its notified-log half holds, where `rdAt`'s contract applies, and closes
at any `soleLog` log), `leaseDels_none` (a lease no key has deletes nothing).

## Second review (2026-10-31, `notes/spec-review/lease-revoke-draft-r2.md`): no blocker

Round 1's R1-R4, R6, R8 confirmed in the code; `deriveRevokeStmt` judged provable resource by
resource; round 1's D3-4 (`roLens`) withdrawn (it would let the members change). Applied:
- F2: the Draft states with its own model, `backendStepR` (the exact revocation), `chainStepR`
  (with `authMayRejectR`: R5 now in the statement) and `certPreR` (the certificate of the exact log);
- F3: the not-found case keeps `ErrLeaseNotFound` (the clause, and `revokeErrIs` in the answer), and
  the answer states the response's `Header` (not nil);
- F7: `revokeLog log id`, and the not-found case's `leaseDels … = []`;
- F1, F6, F9: docstrings (nothing gives `rdAt` yet: `mvcc.New`/`newWatchableStore`'s deleter
  contract at their own names only, L3c's; the lens changes only the buckets; `lessor.Revoke`'s).

Left for Prove (laws, no statement change): F4 `kvWriter_open` moved to txn with the log bound,
`stateAfter_length_le`, `leaseDels_clears`, `leasesKnown_revoke`; F5 `rdAt` into mvcc with intro/use
laws; F8 `eq_of_lt_sorted_mem` proposed to Perennial (`notes/perennial-changes.md`), `stateAfter`
forms. F10 (auth off, an admin request's rejection) is older, noted for L3c.
