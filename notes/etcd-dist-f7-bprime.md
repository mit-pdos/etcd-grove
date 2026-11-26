# F7 option (b') for `authLease`'s `foreign`: false in Go (2026-11-26)

Side branch `etcd-safe-f7-bprime` off `etcd-safe-f7` @ `2313ae318b`; a draft, not to land until Upamanyu
decides. Context: `notes/etcd-dist-f7.md`, "Handoff S5-3".

**(b')**: the dist `foreign` keeps its TimeToLive-with-keys and Leases calls but panics only if a reply
discloses a key the caller may not read ("refused, or the reply's keys are keys the user may read").

**Result: (b') is false for TimeToLive with keys, at a follower applying a snapshot.** Checked before any
change, as asked; so no (b') change was made. The branch now carries option (b) instead (last section).

## Why (Go, pinned etcd `df6af0c36a`)

- `LeaseTimeToLive` (`server/etcdserver/v3_server.go:699`) runs `checkLeaseTimeToLive` (L608) over the
  **receiving member's** lessor (`s.lessor.Lookup(id).Keys()`), then `leaseTimeToLive` (L637): on a follower
  it forwards to the **leader** (`leasehttp.TimeToLiveHTTP`, the leader's handler `leasehttp/http.go:108`
  answers from its own lessor, no auth check) and returns the leader's keys unchecked. Only the auth store's
  revision is re-checked after (L720). So the reply's keys are bounded by nothing the check saw.
- In the workload, barriers after the set-up make every member hold the keys, so plain apply lag is ruled out
  (that is `issues/etcd-lease-timetolive-keys-toctou.md`'s follower case). What remains is the snapshot window
  (`nonissues/etcd-lease-keys-mid-apply.md`, "A second window"): `applySnapshot` calls `lessor.Recover` (leases
  reloaded with empty key sets), then `kv.Restore` re-attaches the keys. A check in between passes over the
  empty set, and the forwarded reply carries the leader's keys. The dist cluster is not in no-snapshot mode
  (`ClusterOk`: `¬ clusterNoSnap`), so this is in the deployment's behaviours.
- Leases (`LeaseLeases`, L738): checks every local lease's local keys (`checkLeaseLeases`) and answers from the
  **local** lessor with lease IDs only (`LeaseStatus{ID}`), no keys, no forwarding. So (b') holds trivially for
  Leases: its reply never carries a key. Whether a lease ID is a disclosure: etcd's check treats listing as
  protected (refused when any lease holds an unreadable key), but the reply names no key; under (b')'s wording
  it discloses nothing. (The same snapshot window makes the *refusal* fail there too, which is (b)'s reason.)
- The leader path: a leader is not normally applying a snapshot; a member that applies one and then wins an
  election can answer from its own half-restored lessor (subset of keys, then `Demoted()` usually refuses,
  per the nonissue). Not needed for the counterexample.

## Evidence: a Go integration test

`notes/etcd-dist-f7-bprime/f7b_lease_keys_snapshot_test.go` (`TestF7bLeaseKeysAfterSnapshot`), run in a
copy of the pinned etcd tree with `tests/integration` (`/shared/tmp/f7b-gotest/etcd`, from
`/shared/tmp/coord-03/f7-s5-gotest/`), go1.27.1, `gofail enable server/etcdserver/`, plus one **test-only
failpoint** `applyAfterRecoverLessor` between `lessor.Recover` and `kv.Restore`
(`notes/etcd-dist-f7-bprime/failpoint.patch`; it only sleeps, widening the window; no upstream failpoint sits
there). Three members, auth on, `SnapshotCount: 10`, `SnapshotCatchUpEntries: 5`; u may read and write `a/`
only; root's lease Lz holds `z/lease`; u's client on follower F. Before: u's TimeToLive(Lz, keys) at F is
refused, u's Get of `z/lease` is refused. F is partitioned, the leader writes 60 keys, the partition heals, F
applies the leader's snapshot; u's TimeToLive(Lz, keys) at F then returns:

```
f7b_lease_keys_snapshot_test.go:105: u's TimeToLive(Lz, keys) at F was not refused; keys: [z/lease]
    Error:      []string{"z/lease"} should not contain "z/lease"
    Messages:   (b') false: the reply discloses a key u may not read
--- FAIL: TestF7bLeaseKeysAfterSnapshot (3.32s)
```

So the dist workload with (b')'s check would panic in a run where u's member applies a snapshot between
`foreign`'s check and the forwarded answer, exactly the case (b') was meant to tolerate.

## What a Lean proof of (b') would have needed (for the record; not added)

`Lease_TimeToLiveOn_dist`'s post would need a reply-keys claim: the reply's keys are readable by the caller.
Since the reply is the leader's and the check the member's, no such law is true of etcd at this pin; it would
be an unsound axiom (the test above refutes it). A sound variant needs the Go fix of
`issues/etcd-lease-timetolive-keys-toctou.md` ("check permission on the keys actually returned", after
`leaseTimeToLive`), on the fork; with that fix the post would be, informally: `resp = ok r → ∀ k ∈ r.Keys,
rangePermitted (authAt Γ mid) user k` (the auth state the revision re-check pins).

## Options left (for the lead)

- (b) narrow the workload (drop TimeToLive with keys and Leases from `foreign`), or keep Leases under (b')
  (trivially true: its reply has no keys) and drop TimeToLive with keys.
- Fix etcd on the fork (re-check the returned keys) and then (b') holds for TimeToLive; the dist spec's post
  gets the claim above, proved through the fixed `LeaseTimeToLive`, or as a reviewed interim axiom.
- (a)/(c) of Handoff S5-3.

## (b) on this branch (2026-11-26; the lead's choice, pending Upamanyu)

Since (b') is false, this branch now carries option (b): the dist `foreign` keeps only the Revoke refusal.

- **Go** (`examples/etcd/dist/client/authlease.go`): `foreign` drops its TimeToLive-with-keys and Leases calls
  (a comment says why, pointing to `issues/etcd-lease-timetolive-keys-toctou.md` and the snapshot window above);
  `RunAuthLease`'s docstring says checks 3-5 are narrowed to 3. The dist `foreign` was already a copy of
  authlease's (`examples/etcd/authlease/authlease.go`), so no single-process file changed. Retranslated
  (`etc/goose.py --project putget-dist`, `--check` clean). `go test ./etcd/dist/` passes, and a short
  `DIST_RUN=1 DIST_WANT=authLease` round (3 members, snapshots 10/5, auth on) ends `authLease: checked`.
- **Spec** (`Spec/.../dist/client/foreign.lean`): the two lessor-read refutation premises go, and with them what
  only they used (`Γ.ls` injective, `m₀`, `lease.lessorLb (Γ.ls mid) m₀`). Left: the Revoke refutation
  (`∀ σ, Qr σ -∗ writeCheckedD [addr] Γ γR (principalOf cfg) (irrLeaseRevoke id) L₀ -∗ R ={⊤}=∗ False`), the
  `writeAuD … (.leaseRevoke id) L₀ Qr` offer and `authPubLbM … n₀`, as `Lease_RevokeOn_dist` takes them.
- **Proof** (`Proof/.../dist/client/foreign.lean`): the Revoke part of the old proof, unchanged; callees
  `reqCtx`, `refused`, `Lease_RevokeOn_dist` (`WithAttachedKeys`, `Lease_TimeToLiveOn_dist`,
  `Lease_LeasesOn_dist` no longer). No `sorry`, no axiom. Not yet linked (no dist `Link` lists `foreign`).
- **Why this is the claim that holds**: Revoke's auth check runs at apply over the replicated auth state
  (`writeCheckedD`), so its refusal holds whichever member receives it; TimeToLive and Leases are checked over
  the receiving member's lessor, which a snapshot leaves keyless for a window. The dist `authLease` claim is
  narrower than the single-process `etcd_authlease`'s (which keeps all three: one process applies no snapshot
  between check and answer).
- **Next**: `RunAuthLease` (Handoff S5-3, option (b)), the cell at the view for the Revoke refutation.
