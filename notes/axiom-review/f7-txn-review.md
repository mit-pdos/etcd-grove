# F7 S5 review: `Txn_CommitOn_dist`'s widened write arm (leased transactions) (2026-11-26)

This review used the `axiom` skill and was read-only. I read `/shared/etcd-grove-f7` at `658cc6075d` and wrote nothing
there. The widening commit `0ebea22657` is an ancestor of that head. The Go source is the etcd pin `df6af0c36a`
(copied from `f7-s5-gotest/etcd`), run with go1.27.3.

**Target.** In `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/TxnCommitOnDist.lean`, the write arm's pure
premise changed:

- before: `txn.txnPlain (txnWireOf b.model)`
- after: `txn.txnPlain … ∨ (Γ.kv.lm = .revocable ∧ txnPlainL (txnWireOf b.model))`

The rest of the statement is unchanged.

## Verdict

**SOUND.** I found no counterexample. Every case the lead asked about behaves in Go as the post and the model step
say:

- A leased transaction either succeeds as one committed `kvOpStep (.txn t)` step, with the leases attached, at the
  revision the post names, and with the grant `writeCheckedD … (irrTxn tw)` true of Go's apply-time check.
- Or it fails without changing the store. Every refusal lands in the error arm, which claims nothing.

The only conditions are the ones `KV_PutOn_dist`'s leased arm already rests on (see "Inherited conditions" below);
the widening adds no new one.

The widening is also exactly the proved single-process contract `client.txnUpdAtOn` (`KVServiceOn.lean:983`):
`txn.txnPlain t ∨ (ρ.kv.lm = .revocable ∧ txnPlainL t)`. There, `txnNestOk` is implied here by `TxnModel.plain
b.model`, which excludes nested transactions. Per member, the Go behaviour is therefore already covered by a proof.
What is left to check is cross-machine: whether every member's lessor agrees with the model's lease table at the
entry's log position. The tests check this, including through a snapshot.

## What the model says (the conditions checked against Go)

| Go (pin) | Model | Agree? |
|---|---|---|
| **Auth check:** `checkTxnPermission` (`apply/auth.go:128-188`) checks the compares, then **both** branches' ops, and for each put `checkPutAuth` = `IsPutPermitted(key)` then `checkLeasePuts(lease)` | `grantedAt` = `kvGranted ∧ leaseGrantedM`. For a txn, `leaseOk` holds for every `o ∈ txnPutsW t`, which covers both branches (`AuthApplyLatestTxn.lean:103`) | yes. Test 6: a foreign lease on the *untaken* branch is refused |
| **`checkLeasePuts`:** `Lookup(id) == nil` passes. Otherwise admin passes, otherwise `IsPutPermitted` must hold on every key in `l.Keys()` | `leaseOk` (`KVAuthModel.lean:338`): auth off, or `adminOk`, or every `k` with `I.lookup k = some id` writable. `I` = `leaseItemsOf (stateAfter (kvModelOn L))` | yes. An empty foreign lease passes; one holding a key outside the user's range is refused; root passes |
| **Lease check:** `checkTxn` (`txn/txn.go:201`) runs on the **taken** branch only. Its `checkPut` → `checkLease` (`put.go:80`) gives `ErrLeaseNotFound` when `Lookup == nil`; `checkAndGetPrevKV` gives `ErrKeyNotFound` for `IgnoreValue` on a missing key | `kvOpStep (.txn t)` commits iff `PathsIgnOk ∧ PathsLeaseOk` on `t.branch (txnOk …)` (`KVModelDefs.lean:1111`), and `PathLeaseOk`'s put case is `l = 0 ∨ l ∈ σ.leases.ids`. Otherwise the step is `σ` | yes. A missing lease on the untaken branch succeeds; on the taken branch it is refused with no change |
| **Writes:** `executeTxn` → `put` → `storeTxnWrite.put`, which detaches the old lease and attaches the new one. All of the txn's writes are at one revision | `σ.commit (srvRunTxn (σ.rev+1) …).2.1`. The post's `m.hdr.revision` is that commit's revision | yes. A success is exactly `r0+1`; a re-put moves the key between leases |
| **Shape:** `txnPlainL` = `txn.txnLeased` (`TxnRun.lean:629`) | gets at rev 0; any lease on `.put`; `.putIgnVal _ l` only with `l.isSome` (IgnoreValue, not IgnoreLease); `putKeep` (IgnoreLease) is excluded; nesting is allowed but `TxnModel.plain` excludes it | test 7: IgnoreValue+lease keeps the value and moves the lease, and on a missing key gives `ErrKeyNotFound` |
| **Duplicate keys:** put(k)+delete(k), or two puts of k | rejected in v3rpc `checkIntervals` before raft: no entry, so the AU does not fire; error arm | yes (`ErrDuplicateKey`, revision unchanged) |

**Why a lagging member cannot diverge.** The lessor changes only at log entries: the grant and revoke applies. In this
deployment lease expiry is also a leader-proposed revoke entry, and checkpoints are off. A follower that installs a
snapshot rebuilds its lessor from the snapshot's backend first (`lessor.Recover`, `server.go:1090`) and then
re-attaches keys in `kv.Restore` (`kvstore.go:393`). So at the txn entry's log position, every member's `Lookup` and
`l.Keys()` agree with `kvLeasesOn`/`leaseItemsOf` at that position.

"Not yet granted there" therefore cannot happen to a txn proposed after the grant's reply: the grant's entry
precedes the txn's in the log, and the serving member replies only after its own apply of the txn's entry (`s.w`).
"Already revoked" means the revoke precedes the txn in the log, which gives `ErrLeaseNotFound` on every member.

## The Go test

The test is `/shared/tmp/coord-03/f7-txn-gotest/etcd/tests/integration/f7txn_leased_test.go` (`TestF7TxnLeased`). It
uses three members with auth on (simple tokens) and `SnapshotCount: 20`, `SnapshotCatchUpEntries: 5`. Users:

- `alice`: read-write on `[a,b)`
- `bob`: read-write on `[c,d)`
- `root`

Each case records the revision before and after the txn. It requires a success to be one revision step that equals
`resp.Header.Revision`, and a refusal to leave the revision unchanged. The output is
`/shared/tmp/coord-03/f7-txn-gotest/test-output.txt`, with the case lines extracted in `cases.txt`. The result was
**`--- PASS: TestF7TxnLeased (1.12s)`**.

Cases 1-8 ran with the client at each member in turn (m0 shown; m1 and m2 gave the same results):

```
two puts, two leases (one granted at another member), a delete   err=<nil>                rev 2 -> 3
put(k, lease) and delete(k) in one branch                         err=duplicate key        rev 3 -> 3
put(k, l1) and put(k, l2)                                         err=duplicate key        rev 3 -> 3
re-put k1 with la2                                                err=<nil>                rev 3 -> 4   (la1 now empty)
missing lease on the taken branch (plus a lease-free put)         err=lease not found      rev 4 -> 4   (lease-free key absent)
missing lease on the untaken branch                               err=<nil>                rev 4 -> 5
revoked lease                                                     err=lease not found      rev 5 -> 5
bob: alice's lease (keys in [a,b)) on the taken branch            err=permission denied    rev 5 -> 5
bob: alice's lease on the UNTAKEN branch                          err=permission denied    rev 5 -> 5
bob: alice's EMPTY lease: allowed (no key to check)               err=<nil>                rev 5 -> 6
alice: le now holds bob's key                                     err=permission denied    rev 6 -> 6
bob: own lease + alice's lease in one txn                         err=permission denied    rev 6 -> 6
root: alice's lease la2 on a key outside alice's range            err=<nil>                rev 6 -> 7
alice: own lease, key outside her range                           err=permission denied    rev 7 -> 7
IgnoreValue + lease on an existing key                            err=<nil>                rev 7 -> 8   (value kept, lease la1)
IgnoreValue + lease on a missing key                              err=key not found        rev 8 -> 8
get + leased put (get reads pre-state)                            err=<nil>                rev 8 -> 9
alice: revoke la2 (root attached a key outside her range)         permission denied    (then root's revoke deletes all la2 keys at one revision)
```

Case 9 (lag), 20 rounds: alice grants at m0 and immediately sends a leased txn through m1 and m2; all succeed. She
then revokes at m0 and immediately sends a leased txn through m1 and m2; all fail with `ErrLeaseNotFound`.

Case 10 (snapshot): a follower was stopped. While it was down, the cluster:

- granted `lpre` before the stop and attached `asnap-pre` to it;
- granted `lgr` and attached `asnap-k`;
- granted and revoked `lrv`, and revoked `lpre`;
- ran 60 more writes.

The follower was then restarted (log: `applied snapshot … incoming-leader-snapshot-index 390`), and txns were sent
through it at once:

```
snapshot member 1: leased txn with lease granted while down: <nil>
snapshot member 1: leased txn with lease revoked while down: requested lease not found
snapshot member 1: leased txn with lease granted before, revoked while down: requested lease not found
snapshot member 1: bob attaching alice's lgr (keys restored from snapshot): permission denied
member 2 (never down): bob attaching alice's lgr: permission denied
member 0/1/2 serializable view of asnap*: asnap-1@…  asnap-k@…  rev 152   (identical on all three)
```

## Inherited conditions (as for `KV_PutOn_dist`'s leased arm; none new)

1. **`Γ.kv.lm` must be the serving member's lease mode, and `Γ.ls` its lessor.** This is P-L1 in the proposed Serve
   (`f7-c.md` F2, closed in `f7-rerev-c.md`). The widening reads only `Γ.kv.lm`.
2. **No crash-restart serving in the revocable auth-on mode** (`f7-rerev-c.md`'s limit: `lessorSlot` closes once).
   The test restarts a member, which is outside the proof's no-crash deployment. It shows only that Go stays
   consistent there; it is not a case the axiom must cover.
3. **The retry semantics are those of the plain write arm.** `writeAuD` is `□`, so a token-refresh resend is
   covered. `ErrLeaseNotFound` fires the AU as a no-op step (`kvOpStep … = σ`), and its `Q σ` is dropped in the
   error arm. Nothing new here.

## Observations (no change requested)

- **A user can be locked out of revoking their own lease** (case 8's tail). Once root or another user puts a key
  outside the owner's range on the owner's lease, the owner's `Revoke` is refused (`checkLeasePuts`). This is
  documented etcd behaviour, not this axiom's concern: `Lease_RevokeOn_dist` claims nothing on refusal.
- The `outTokOk` / `authorization` gap of `f7-s5-review.md` (1') applies to this contract as to the other 12. It is
  independent of the widening, and its fix is in that review.

No issue was found in the verified Go code, so there is no `issues/`/`nonissues/` entry.
