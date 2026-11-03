# Review: the lease-revoke Draft (D1–D6 of `notes/lease-revoke-plan.md`)

Reviewer: independent spec review, 2026-10-31. Worktree `/shared/etcd-grove-leaserevoke`, branch
`lease-revoke` at `5879096ea3`. The plan is uncommitted (`?? notes/lease-revoke-plan.md`). The
Draft is not in code yet, so I judged the statements as the plan writes them, against the Go code
at the etcd pin (`.lake/go-src/etcd`) and the current Lean definitions. Paths below are relative to
the worktree. `apply/` is `Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/`.

## Summary

The Draft's direction is right: the outcome is exact (`revokeDels`), the effect on the lease bucket
goes through `E.RO` as `isCluster` does, the range deleter is a premise (F2 (a)), and the class is
the item map before the call. D1's two claims hold. Six findings need a change before Freeze. Two
of them block the D3 derivation as written.

1. **Blocker (D1 with D3).** The certificate premise D3 inherits from `lessor.Revoke.spec` asks for
   *every* list of deletions. Once D1 makes `backendStep` exact, `certPre` certifies only one list,
   so nothing can supply the premise.
2. **Blocker (D3/D4).** The `γw` that `rdIs` is stated at is not tied to the watchable names that
   `kvWriter`'s `wlogOwn` holds the notified log at. Without that tie, `watchWriter γw log` cannot
   be built.
3. **Major (D2/D6).** Admitting the request in `rqOk` breaks `uberApplier.dispatch`'s proof and the
   server's proofs. D6 says dispatch is unchanged, but its spec takes `rqOk` and has no
   `revokeRes`.
4. **Major (D5).** "`alarmRevoke` as `alarmPut`" is false of Go. The capped and quota appliers do
   not touch `LeaseRevoke`.
5. **Major (D4/D5).** The `RO` effect is an existential the client cannot resolve, and the answer
   does not say which error came back. `dispatch.spec` already wants a deterministic `RO` effect.
6. **Major (D5).** With auth off the chain still admits an auth rejection of a revocation. Go never
   rejects one with auth disabled, and the server's deterministic model assumes no rejection.

Ranking by need of revision: **D3 > D5 > D4 > D2 > D1**.

---

## D1: `revokeDels` and `backendStep .leaseRevoke`

### What is good

- The outcome becomes a function of the state, as T2 did for put, delete and txn. That is the
  stronger spec, and the KV model can use it directly (`KVModelDefs.backendLog`).
- The `id = 0` guard is needed and correct. `leaseItemsOf` maps no key to `0` (`kvLease`,
  `storage/mvcc/LeaseItems.lean:29`). Without the guard, `filter (lease = 0)` would delete every
  key that has no lease.
- **Claim "a lease that is not live has no key": verified.** `leaseClosers` carries
  `⌜∀ it id, I.lookup it = some id → id ∈ L⌝` (`lease/InvLessor.lean:631`) at
  `I = leaseItemsOf (stateAfter log)`. The same fact follows from `txn.leasesKnown L` alone
  (`leaseOk L l := l = 0 ∨ l ∈ L`, `txn/Write.lean:192`), which the clause already takes. Either
  way, for `id ∉ L` and `id ≠ 0` no state entry has lease `id`, so `revokeDels = []` and
  `commitLog log [] = log`.
- **Claim "`revokeDels` = `lessor.Revoke`'s sorted `ks`": verified, modulo one order lemma.**
  - `ks` is `Nodup`, sorted by `GoStringLe`, and has exactly the keys `k` with
    `(leaseItemsOf (stateAfter log)).lookup ⟨k⟩ = some id` (`Spec/.../lease/lessor__Revoke.lean`).
  - `leaseItemsOf s` looks a key up by `findKey`, the first match (`Model.lean:127`). The state's
    keys are strictly sorted (`stateAfter_sorted`, `mvcc/LogLemmas.lean:459`, `etcdKvLess` =
    `GoStringLt` on keys), so `findKey` returns the unique entry. Hence, for `id ≠ 0`, the keys
    of `s.filter (lease = id)` are exactly `ks`'s members, in increasing order.
  - Two strictly sorted lists with the same members are equal. This needs `GoStringLt` irreflexive
    and transitive (bytewise, as `sort.StringSlice` compares). I did not check that Perennial
    exports this lemma.
- Go's not-found path returns before any write (`lessor.go:326-333`), so `.applied log false` with
  the lessor's error is the right outcome.

### Findings

**D1-1 (minor; a margin to state).** `revokeChanges_eq` (D1's last sentence) holds only under the
server's invariant. `backendLog` decides by `id ∈ lt.ids` (`KVModelDefs.lean:314-317`), D1 by the
state. They agree only when every nonzero lease of the state is in `lt.ids`, and `0 ∉ lt.ids`
(`leaseGrantOk`, `KVModelDefs.lean:268`). *Change:* write the lemma with both premises:

```lean
revokeChanges_eq : (∀ v ∈ s, v.lease ≠ 0 → v.lease ∈ lt.ids) → 0 ∉ lt.ids →
  (if id ∈ lt.ids then revokeChanges s id else []) = revokeDels s id
```

**D1-2 (moderate; vocabulary, see also D3-1).** `revokeDels` lives in `apply` (the plan says
`apply/Chain.lean`), but the lessor's spec needs the same function (D3-1).
*Change:* define it once where `lessor.Revoke.spec` can use it, e.g. `mvcc.leaseDels s id` next to
`leaseItemsOf`. Export the law clients need, so that no client unfolds it:

```lean
leaseDels_mem (h : Sorted s) : .del k ∈ leaseDels s id ↔ (leaseItemsOf s).lookup ⟨k⟩ = some id
```

`chain_revoke`'s client needs this law to turn `reqLeaseClass` (stated on the item map) into
"every key the revocation deleted was writable", which is the stage's stated goal. Without it the
client unfolds `revokeDels` and `leaseItemsOf`, which the principle "a client does not unfold"
forbids.

---

## D2: `rqOk .leaseRevoke := putOk log`

### What is good

- The bound is exactly what the code needs. `lessor.Revoke.spec` takes `log.length + 4 ≤ 2^63`
  (= `putOk`) and `(stateAfter log).length ≤ 2^62`. `rdIs` takes the first again
  (`InvWatchStore.lean:1842`).
- The second bound is rightly derived rather than assumed: `soleWriter_small'`
  (`txn/SoleWriter.lean:100`) gives fewer than `2^48` changes, and a new `stateAfter_length_le`
  bounds the state by the puts. Plausible; the new lemma is not yet written.

### Findings

**D2-1 (major; the ripple D6 misses).** `rqOk` is the workload predicate.
- Today `rqOk .leaseRevoke = False` rules the case out in proofs outside the chain:
  - `apply/uberApplier__dispatch.lean:545-551` (the generic dispatch, not `DispatchKVL`);
  - `apply/newApplierV3Capped.lean:168`;
  - `apply/applierV3backend__LeaseRevoke.lean` (vacuous);
  - the server's `KVApply.lean:94`, `ApplyNormalOn.lean:49`, `InvApplier.lean:115` and
    `EtcdServer__applyEntryNormal.lean:1106/1284`.
- `apply.uberApplier.dispatch.spec` (`Spec/.../apply/uberApplier__dispatch.lean:41-60`) takes
  `⌜rqOk log rq …⌝`, `E.RO rs`, and returns `E.RO (restAfter rq v3 rs)`.
- With D2 that proof must call the chain's `LeaseRevoke`, which needs `revokeRes` (the range
  deleter). Dispatch's pre does not have it. Its post's `restAfter` would also need the liveness
  bit, which the apply layer does not have (D4-1).
- So D6's claim "`uberApplier.dispatch` is unchanged" holds only of `DispatchKVL` (`isKVKind`). It
  is false of `uberApplier.dispatch.spec`, and the change reaches the server, out of the chosen
  scope.

*Change:* leave `rqOk .leaseRevoke = False` (the workload still sends none: F3, `plainCover`). Put
the bound in `revokePre` itself:

```lean
revokePre … := ⌜rq.leaseRevoke = some id ∧ dispatchKind rq = .leaseRevoke ∧ putOk log⌝ ∗ …
```

`chain_revoke` then needs nothing of `rqOk`. Dispatch and the server admit the kind at L3c, when
their specs gain the range deleter and the liveness. Alternatively, keep D2 and list in D6 the
change to `dispatch.spec` (pre: `revokeRes`; post: `restAfter` with the liveness) and the server
proofs above. That is out of the decided scope.

---

## D3: the `Revoke` clause of `isApplyLessor`, and the `RO` parameter

### What is good

- The clause is no longer vacuous. Its shape follows the proved `lessor.Revoke.spec` closely:
  - the case split on `id ∈ L`;
  - `Pre` back in the not-found case and `Post` in the live case (Go opens the write transaction,
    which runs the hook, even when there are no keys);
  - `storeWT` back only in the not-found case;
  - the live set filtered, and `leasesKnown` re-established at `log'`.
- The bucket effect goes through `RO` with `restRevoke` (`apply/RestLease.lean`, `revoke_bk` is
  `rfl`). This is the pattern `isCluster` set (`apply/Contracts.lean:491-516`), and the lens is
  only a premise of the derivation, so the clause names no backend.
- **`storeWT` not returned in the live case: correct.** `lessor.Revoke.spec`'s live branch does not
  return it; the write transaction spends it, as `kvPost` does for a put.
- **Lease id 0:** Go answers `ErrLeaseNotFound`, since `Grant` refuses `NoLease`
  (`lessor.go:283-285`) and `leaseMap[0]` is nil. The clause covers this through `id ∉ L`, and
  `revokeDels _ 0 = []` agrees even if `0 ∈ L`.
- `rd ≠ nil` comes from `rdIs` (`InvWatchStore.lean:1841`). This rules out Go's `le.rd == nil`
  early return (`lessor.go:338-340`). Revoking twice without a deleter would close `revokec`
  twice; that case is already filed as `nonissues/etcd-lessor-revoke-twice-no-deleter.md`.

### Findings

**D3-1 (blocker; a premise its supplier cannot prove).** The clause takes
`□ ∀ pend, ⌜∀ c ∈ pend, c.isDel⌝ -∗ mvcc.certOkNext γ log pend`, which comes from
`lessor.Revoke.spec`. Its supplier is the backend's `LeaseRevoke`, which has only
`certPre E .backend rq log`: the certificate of `oc.logAfter log` for each `oc` that `backendStep`
admits (`apply/Chain.lean:858-861`).
- Under the old `backendStep` (`∃ pend` of deletions, `Chain.lean:226`) those matched.
- Under D1 `certPre` certifies exactly `commitLog log (revokeDels (stateAfter log) id)`, so the
  `∀ pend` premise cannot be discharged.
- At the server it is false anyway: `certOk` says the log is the model of the committed raft log,
  which is one log, not every log of deletions.

This is the "a premise must be provable by whoever supplies it" lesson
(`examples/auth-history-tie.md`, critique 1).

*Change:* restate `lease.lessor.Revoke.spec` (a proved spec, so no axiom moves) at the actual
deletions, and strengthen its post in the same step:
- pre: `mvcc.certOkNext γw.st log (mvcc.leaseDels (mvcc.stateAfter log) id)`;
- live post: `watchWriter γw (commitLog log (leaseDels (stateAfter log) id))` in place of
  `∃ ks, …`. The sorted-equality argument of D1 moves into the lessor's proof, once.

The clause then takes `mvcc.certOkNext γ log (revokeDels (stateAfter log) id)`. The backend's
proof gets it from `certPre_backend_applied` and `certOkNext_of_commitLog` (`Chain.lean:905-930`).

**D3-2 (blocker; two sets of watchable names).** The clause takes `txn.kvWriter s γ log` and
`mvcc.rdIs rd ws s γw ∗ ⌜γw.st = γ⌝`.
- `kvWriter`'s `wlogOwn` (`txn/Defs.lean:102-106`) holds the notified log at its own existential
  `∃ ws₂ γw₂`: `monoListAuthOwn γw₂.wlog ½ log`.
- `lessor.Revoke` needs `watchWriter γw log`, that is `monoListAuthOwn γw.wlog ½ log`, at the same
  `γw` as `rdIs` (`InvWatchStore.lean:1747`). `rdIs` is stated at one fixed `γw`, and its post
  `isWatchTxnWrite tw ws st γw` carries `watchStoreInv ws γw`.
- What exists: `watchableStore_unique` (`txn/KVWrite.lean:134`) and `isWatchableStore_agree`
  (`SnapApplyOpen.lean:68`) prove only `ws₁ = ws₂`, not `γw = γw₂`. I found no lemma that equates
  the names (grep for name agreement in `storage/mvcc` and `txn`).
- `txn.kv_Write` gets around this because its `Write` hypothesis is quantified over the names: it
  is applied at `γw2`, `KVWrite.lean:203-217`. `rdIs` is not quantified that way.

As drafted, the derivation cannot produce `watchWriter γw log`. (Uncertain whether a names
agreement is provable from `isWatchableStore`; I think not, since two mutex guards with different
invariants do not identify them.)

*Change, either:*
- (a) state `rdIs` for every name set over the store, which is how `txn.kv_Write` uses `Write`:
  ```lean
  revokeRes … := ∃ rd, lease.rdOwn E.γ.leases rd ∗
    □ (∀ ws γw, ⌜γw.st = E.γ⌝ -∗ mvcc.isWatchableStore ws E.s γw -∗ mvcc.rdIs rd ws E.s γw)
  ```
  The server's closure calls `s.KV().Write()`, whose spec is quantified this way, so `BuildLemmas`
  can prove it.
- (b) pin the watchable names at `ws` (a `lessorPin`-like ghost pin inside `isWatchableStore`) and
  export `isWatchableStore ws s γ₁ ∗ isWatchableStore ws s γ₂ ⊢ ⌜γ₁ = γ₂⌝`.

(a) stays inside the stage; (b) changes `mvcc`.

**D3-3 (moderate; error and RO not tied).** The post's top-level `applyErrIs err` loses what
`lessor.Revoke.spec` gives:
- the not-found branch has `err = ErrLeaseNotFound` (its global, `GoInterface.ok e`, so non-nil);
- the live branch has `err = nil`.

D3 keeps `err = nil` in the live branch but drops `err ≠ nil` from the not-found branch, so the two
branches cannot be told apart by `err`. That is what D4/D5 then need (D4-1).
*Change:* in the not-found branch add `⌜err ≠ GoInterface.nil⌝` (or the
`globalAddr ErrLeaseNotFound ↦□ …` fact), so that `err = nil ↔ id ∈ L`.

**D3-4 (minor; derivation premises).** The derivation's new premises are reasonable: watchable,
`hookOk`, the lens. Two notes:
- The lens is `roLens` (`etcdserver/InvRest.lean:395`) at
  `X rs = storeRb γ rs.bk ∗ lessorBeOn lp d.be`, with `RO {rs with bk}`. Reuse that definition
  instead of writing it out.
- `Grant` and `Checkpoint` still write the same bucket through `RW` while `Revoke` writes through
  `RO`. Say in the docstring that this asymmetry is deliberate until grants are admitted.

---

## D4: `revokePre`'s extra resource, and the post

### What is good

- Option (a) of F2 keeps the range deleter out of `kvOwn`, and so out of the server's snapshot path.
  That matches the decided scope.
- Taking `E.RO rs` per call and returning it is the same footprint `dispatch.spec` and `isCluster`
  already use. It is an aggregate, but an indexed one whose effect is a named function, so a new
  bucket does not change the text.

### Findings

**D4-1 (major; the existential the client cannot resolve).** "`rs' = restRevoke id rs` or `rs`
(`∃`, with `err = nil` in the first)" leaves the client unable to tell which happened:
- `err = nil` with `rs' = rs` is admitted;
- `oc` is `.applied log false` both for a live lease without keys and for a lease that is not
  found;
- `kvOwn` hides `L`.

Go is deterministic here: `err = nil` exactly when the lease was live, and then the record is
deleted. The consumer already waiting for this is `dispatch.spec`, whose post is
`E.RO (restAfter rq v3 rs)`, a function, so it cannot absorb an existential. This breaks "know the
margin" and "the post says what the caller inspects" (the server tests `err`).

*Change (with D3-3):*
- `revokeResAfter E id rs err := (∃ rd, …) ∗ E.RO (if err = GoInterface.nil then restRevoke id rs else rs)`;
- in `revokeOutcomeIs (.applied _ _)`: `⌜err = GoInterface.nil⌝ ∨ (⌜err ≠ GoInterface.nil⌝ ∗ ErrLeaseNotFound's fact)`.

The rejected outcomes have `err ≠ nil` already (`rejErrIs`), so the `if` gives `rs` there. L3c will
still need `err = nil ↔ id ∈ lt.ids`. Record in the plan that this needs `L` to become visible to
the server, for instance `leasesLive` indexed by the live set. That is the margin of this stage.

**D4-2 (blocker, shared with D3-2).** `revokeRes`'s `∃ rd ws γw, rdOwn ∗ rdIs rd ws E.s γw ∗ ⌜γw.st = E.γ⌝`
inherits D3-2. *Change:* as D3-2 (a).

**D4-3 (minor; vocabulary).** `revokeRes` shows `chain_revoke`'s client the lessor's `rdOwn` and
mvcc's `rdIs`. *Change:* name the pair in the lessor's API, e.g. `lease.rangeDeleterAt γl s γ`.
The server then produces one predicate (from `BuildLemmas`, and later from `Recover` once F2 is
fixed), and the apply package mentions one name.

**D4-4 (minor; margin).** `storeWT` comes back from D3 in the not-found case, but `revokePre`'s post
drops it, as `kvPost` does for every outcome. That is consistent with put. State it as the margin
("the token is spent even when nothing is written").

---

## D5: `chain_revoke`

### What is good

- The shape matches `chain_put` (`apply/Results.lean:213-224`): outcome, answer, `kvOwn` at
  `oc.logAfter log`, `chainRes`, `Post ∨ Pre`, and the class guarded by `authPassed oc`.
- `reqLeaseClass` at the item map *before* the call is right. `checkLeasePuts` runs before the
  backend (`apply/auth.go:191-195`). `reqLeaseClass .leaseRevoke` is already
  `leaseKeysClass … id` (`apply/AuthClass.lean:552`), and a lease the lessor does not have
  attaches no key, so the not-found case holds vacuously.

### Findings

**D5-1 (major; false as specified).** "`alarmRevoke` … the chain's rejections (auth, no space,
corrupt) as `alarmPut`" is wrong about Go:
- `applierV3Capped` overrides only `Put`, `Txn` and `LeaseGrant` (`apply/capped.go:33-44`);
- `quotaApplierV3` overrides only `Put`, `Txn` and `LeaseGrant` (`quota.go:36-54`).

A revocation is therefore never rejected for no space and never gets `ErrNoSpace` after it. The
model already says so: `cappedRejects .leaseRevoke = false`, `quotaChecks .leaseRevoke = false`,
and `chainStep .quota` passes through (`Chain.lean:138-199`). Copying `alarmPut`'s
`ns → .rejected .noSpace` and `quotaAfter` would state outcomes the chain cannot produce, and the
client would have to discharge them.

*Change:*

```lean
def alarmRevoke (cr : Bool) (id : w64) (log : mvcc.Log) (o : Outcome) : Prop :=
  if cr then o = .rejected .corrupt
  else o = .rejected .auth ∨ o = .applied (mvcc.commitLog log (revokeDels (mvcc.stateAfter log) id)) false
```

There is no `ns` parameter; with D5-2 the `.rejected .auth` disjunct also gets the auth mode.

**D5-2 (major; the client cannot discharge it).** In `chainStep`'s auth case,
`authMayReject on rq` is always true for a revocation, because its third disjunct holds for every
kind but put, range, deleteRange and txn (`Chain.lean:165-168`). So `chain_revoke` admits an auth
rejection with auth off.
- Go with auth disabled: `checkLeasePutsKeys` returns at `as.IsAdminPermitted(ai) == nil`
  (`auth.go:208-212`; disabled, it returns `nil`, which `authMayReject`'s own docstring records).
  `checkLeasePuts` with no lease returns `nil`. A revocation is never rejected.
- The server's deterministic model assumes no auth rejection (`chainLog (.auth _ c) = chainLog c`,
  `KVModelDefs.lean:356`). L3c, with auth off, could not connect `chain_revoke`'s outcome to
  `backendLog`.

*Change:* add `dispatchKind rq ≠ .leaseRevoke` to the third disjunct of `authMayReject`, so that a
revocation is rejected only with `on = true`. Prove `authApplierV3.LeaseRevoke`'s no-rejection
with auth off from `isAuthStore … false`, as for put. Then `alarmRevoke` takes `on` and has
`(on = true ∧ o = .rejected .auth)`.

**D5-3 (moderate; the answer is weaker than the code).**
`applierV3backend.LeaseRevoke` returns `&pb.LeaseRevokeResponse{Header: a.newHeader()}` even when
`err ≠ nil` (`apply/backend.go:94-97`). `newHeader` reads `KV.Rev()` after the deletion
(`backend.go:306-313`). `revokeOutcomeIs (.applied _ _)` says nothing of `resp`. The server's
`LeaseRevoke` answers the client with that header (L3c/L4), as put does with `appliedHdr`.
*Change:* in the applied case add `⌜resp ≠ null⌝`, the header's revision, and the header's id
fields owned, by analogy with `putAnswerIs`/`appliedHdr` (`Chain.lean:801-830`). Or record it in
the docstring as the margin, if L4 will get it elsewhere.

**D5-4 (minor).** The post also needs `revokeResAfter` defined (D4-1). With D2-1, `revokePre`
carries `putOk` and no `rqOk`. Add the `leaseDels_mem` law (D1-2), so that the client can conclude
"every deleted key was writable" without unfolding.

---

## Other observations (not targets)

- **F3's wording.** "`Recover` empties the live set": Go's `Recover` reloads every lease record from
  the new backend's `lease` bucket (`initAndRecover`, `lessor.go:808-835`). The live set is empty
  only under `lessor.Recover.spec`'s premise that the bucket is empty
  (`Spec/.../lease/lessor__Recover.lean:65`), which the workload gives. *Change:* say "under the
  workload (no grant, so an empty lease bucket)".
- **F2 (`Recover` and `rdOwn`)** is correctly recorded as false in `notes/audit.md:381` (it is a bug
  in this repository's spec, so it belongs in `notes/`, not `issues/`). I confirmed it: Go writes
  `le.rd = rd` at `lessor.go:605`, and the axiom's pre/post have no `rdOwn`.
- **No new bug in the Go code.** `le.rd == nil` with a double revoke is already in
  `nonissues/etcd-lessor-revoke-twice-no-deleter.md`.

## Ranking by need of revision

1. **D3**: two blockers. D3-1, the certificate premise, requires restating `lessor.Revoke.spec` at
   the actual deletions. D3-2 is the names mismatch. D3-3 drops the error of the not-found branch.
2. **D5**: `alarmRevoke` is false as written (D5-1). The auth-off rejection is a disjunct the
   client cannot discharge (D5-2). The header is missing (D5-3).
3. **D4**: the existential `RO` effect (D4-1) and the names (D4-2, via D3-2).
4. **D2**: the bound is right, but its place (`rqOk`) drags dispatch and the server in. Contrary to
   D6's claim, `uberApplier__dispatch.lean:545-551` uses it.
5. **D1**: correct, and both claims verified. It only needs the lemma's premises written out and
   the function moved where `lessor.Revoke.spec` can use it.
