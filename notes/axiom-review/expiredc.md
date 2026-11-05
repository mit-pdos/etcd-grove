# The lessor's expired-leases channel (axiom review, 2026-11-05)

**Reviewed** (branch `lease-expiry` at `f5eec16dd1`, the lease-expiry plan's X3/X4, "Plumbing:
Part X-a"): the trusted contract `lease.lessorExpiredC lp GA` (`Proof/go_etcd_io/etcd/server/v3/
lease/LessorBackend.lean`), given by the axiom `lease.NewLessor.wp_proof`
(`Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`), and its payload

    ⌜¬ leasesNoExpiry⌝ ∗ expiredLeases GA ls
    expiredLeases GA ls := ∃ ps, ⌜ps ≠ []⌝ ∗ ls ↦*□ ps ∗
      [∗list] p ∈ ps, ⌜p ≠ null⌝ ∗ ∃ id, lsF "ID" p ↦□ id ∗ GA id

with how it is used: `lessor.ExpiredLeasesC.spec` (proved from it), `srvGrantGuard lg on :=
⌜lg = true ∧ on = false⌝` and `srvGrantGuard_expired` (`etcdserver/InvApplier.lean`), `lessorOk lg on
l` and `lessorOk_of_lessorInv` (`etcdserver/LessorOk.lean`), and `EtcdServer.run`'s expiry arm
(`EtcdServer__run.lean`, the `leases := <-expiredLeaseC` clause: `none` dead by the guard, `mono` dead
by `leasesNoExpiry`, `revocable` to the names-only `revokeExpiredLeases`).

Go at the etcd pin `673da07c8` (`server/lease/{lessor,lease}.go`, `server/etcdserver/server.go`),
`GOTOOLCHAIN=go1.27.3`.

## Verdict

**Survives.** Every claim of the payload holds of the Go code; no program found that panics and has
a proof from it. Go checks: `examples/axiomcx/expiredc/expiredc_test.go` (tests only, no Goose
project).

## Claims and attacks

| # | claim / attack | result |
|---|---|---|
| 1 | **Never empty** (`ps ≠ []`, which the `none` mode's dead arm needs: an empty slice meets any guard). | `revokeExpiredLeases` sends only under `if len(ls) != 0` (`lessor.go:652`), on the same `ls`. The only sender on `expiredC` (`lessor.go:656`; `expiredC` set once, `:237`, never closed: `Stop` closes `stopC`/`doneC`), so a receive is always a sent value. Test: every slice non-empty. |
| 2 | **Read-only slice** (`ls ↦*□ ps`). | `ls` is `findExpiredLeases`' fresh `make([]*Lease, 0, 16)` plus `append`s (`:729-749`), a local of one loop iteration; after the `select` (sent, stopped, or dropped by `default`) the loop never touches it; the next iteration makes a new one. Capacity beyond `len` is not covered by `↦*□`. The server's `revokeExpiredLeases` only ranges over it (`server.go:877`). Test: every received slice compared to its copy after further sends, Renew, Demote/Promote and Revokes: unchanged. |
| 3 | **Non-null elements**. | `findExpiredLeases` appends `l` only when `expireExists` returned `next = false` and `l != nil` (`:731-737`); `expireExists` returns a nil `l` only with `next = true` (stale item: `:707-711`) or at the end. |
| 4 | **`ID` read-only** (`lsF "ID" p ↦□ id`). | Written only at construction (`NewLease`, `lease.go:44`; `initAndRecover`, `lessor.go:821`; `FakeLessor`, not used). No `.ID =` and no whole-struct store `*l = …` on a `*Lease` in `server/lease` or elsewhere in `server/` (grep at the pin; `*lease.Lease` users outside the package, `apply/auth.go:207`, `v3_server.go:751`, `server.go:860`, only read). The proved model agrees: `lessor.Grant` and `Recover` persist the field (`LessorLemmas.lean:395-399`, `LessorRecover.lean`), `InvLessor.lean:369` keeps `↦□`, so no proved code holds a full `↦` that the payload's `↦□` would contradict. Test: IDs unchanged after the send. |
| 5 | **`GA id` of each** (a lease never granted cannot appear). | Elements come from `le.leaseMap[item.id]` read under `le.mu.RLock` (`:645-649`, `:706`). Entries enter the map only by `Grant` (`:311`, `NewLease(id, …)` at key `id`: under `leaseGranted`, i.e. `GA`, `lessorAuth`) and `initAndRecover` (`:820`, key `= ID`), reached from `newLessor` (the spec's premise: the `lease` bucket empty) and `Recover` (now proved; its pre takes `□ leaseGranted γl id` for every reloaded record). `Promote`/`Demote`/`Renew`/`Checkpoint`/`Attach`/`Detach`/the loop only change expiries or items (`:486-488`, `:540`). Key and `ID` agree on every insertion, so `GA` of the key is `GA` of the field. |
| 5a | **Stale notifier items after `Recover`** (`Recover` makes a new map but `initAndRecover`'s `leaseExpiredNotifier.Init()` only re-heapifies: the old ids stay). | `expireExists` looks the id up in the *current* map: absent → unregistered, skipped; present → that is a reloaded lease (granted, by `Recover`'s pre), whose expiry is `forever` until the next `Promote`. Tests: after `Recover` onto an empty backend nothing more is sent; leases reloaded from another lessor's backend are sent only after a `Promote`, with their own IDs. |
| 5b | **`Revoke` races** (a lease sent, then revoked). | The payload is persistent and taken at the find; a revoked lease's `ID` stays and `GA` stays. Harmless (the server's revoke of a gone lease returns an error, a different spec). |
| 6 | **Fires under `leasesNoExpiry`** (a slice sent without an expired lease). | Only `l.expired()` leases are appended (`Remaining() <= 0`; `forever` gives `MaxInt64`). `leasesNoExpiry` is stated by "the clock the expiry loop reads" over every lessor of the program, including leases reloaded by `Recover` (the 2026-11-02 rewording, `lease-grant-lessor.md` 3.6). The expiry arithmetic: `MaxLeaseTTL` (9e9 s) times `time.Second` fits `int64`, so `refresh` does not wrap to the past; earlier review's `TestExpiryOnlyLater` covers the moves. Survives (as before). |
| 7 | **The guard pinned per lessor**: a caller choosing `GA := False` and still seeing a slice. | Then no `Grant` can insert (needs `GA id`), `Recover` needs `leaseGranted` for each record (so none), and `NewLessor`'s bucket is empty: Go's map stays empty, nothing is sent. |
| 8 | **The server's use**: `srvGrantGuard_expired` reads `lg = true ∧ on = false` off the first element; `run`'s `none` arm then contradicts `isServerC_lg`. | Sound given 1 and 5 (the guard ignores `id`). `revokeExpiredLeases` reads only `curLease.ID` (`server.go:900`), which 4 covers. |
| 9 | **Revoke-rate edge cases** (`leaseRevokeRate/2 = 0` makes the limit never reached; a negative `ExpiredLeasesRetryInterval` re-finds the same lease). | Duplicates in a slice or a loop that does not end, never an empty or nil-holding slice: no payload violation (a hang is no counterexample). `leaseRevokeRate` is unexported: outside the package always 0, defaulted to 1000. |

## Not tried

A Lean proof (no refutation to prove); `revokeExpiredLeases`' own (names-only, `srvRevokeOpen`)
contract; multi-member promote/demote timing beyond the earlier review's `TestExpiryOnlyLater`.

## Go checks

`examples/axiomcx/expiredc/expiredc_test.go`, at `GOTOOLCHAIN=go1.27.3` and the examples' etcd pin
(`673da07c8`):

```
=== RUN   TestExpiredSlices
    expiredc_test.go:115: rate 1000: 3 slices, 82 leases, all non-empty, non-nil, granted, unchanged
--- PASS: TestExpiredSlices (3.64s)
=== RUN   TestRecoverEmpties
    expiredc_test.go:147: after Recover onto an empty backend: nothing sent in 2 s
--- PASS: TestRecoverEmpties (4.51s)
=== RUN   TestRecoverReloaded
    expiredc_test.go:172: reloaded leases: none before Promote, 3 slices after, IDs among the reloaded
--- PASS: TestRecoverReloaded (4.72s)
PASS
```

(A first version of `TestExpiredSlices` hung: `Renew` of an expired lease waits for its revocation,
`lessor.go:416-424`, which a standalone lessor never does; a block, not a panic, and outside this
payload: `Renew`'s own axiom, `notes/audit.md`. The test now renews a live lease.)
