---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22123 issue open: this bug
  - etcd-io/etcd#22124 pr open: fix of #22123 (keep `leaderKey`/`leaderSession` when the transaction fails)
  - etcd-io/etcd#22437 pr closed: another fix of #22123 (unmerged)
  - etcd-io/etcd#21128 issue closed: related, not this bug (a failed `Campaign` forgets its key); `issues/etcd-election-campaign-error-orphan-key.md`
  - etcd-io/etcd#21165 pr open: fix of #21128; its `Resign` on a failed campaign forgets the key again if that `Resign` fails
---

# concurrency: a failed `Election.Resign` forgets the leadership while the key stays in etcd

- **Status**: a bug (present at the pin). A leader whose `Resign` fails keeps its key in etcd, so
  stays etcd's leader, while the `Election` no longer names it and a retry is a no-op. Reproduced by a
  Go test.
- **Where**: `client/v3/concurrency/election.go` at the etcd pin `107edf7e4` (`etc/goose.py`):
  `Election.Resign` (lines 132-145) clears `e.leaderKey` and `e.leaderSession` (lines 142-143)
  whether or not its guarded delete (line 138) succeeded; on the next call `leaderSession == nil`
  returns `nil` at once (lines 133-135). `Campaign` calls `Resign` on its own failure paths and
  ignores its error: after a failed `Proclaim` (line 87) and after a canceled wait (line 98, with
  `client.Ctx()`).
- **What happens**: a leader calls `Resign(ctx)`, and the transaction fails (a canceled or expired
  `ctx`, a connection error) before reaching etcd. `Resign` returns the error, but `Key()` is now
  `""`, and calling `Resign` again returns `nil` without issuing a request. The key stays in etcd on
  the session's lease: `Leader()` still reports this process, every other candidate waits behind
  it, and the only remaining way to remove it is to close the session (which also drops every
  other key on the lease). Reproduction (a unit test with fakes, package `concurrency_test`, at the
  pin): `issues/etcd-election-resign-error-forgets-key/resign_error_forgets_key_test.go` (dropped
  into `client/v3/concurrency/`; from `client/v3`: `GOTOOLCHAIN=go1.27.1 go test ./concurrency
  -run '^TestResignErrorForgetsKey$' -count=1 -v`). A fake `KV` whose next `Commit` fails without
  touching the store. At the pin it fails:

  ```
  first Resign: injected: request failed before reaching etcd; keys: map[/el/10:true]; Key()=""
  second Resign: <nil>; txns issued: 0; keys: map[/el/10:true]
  leader key "/el/10" left in etcd after a failed Resign and a retry (retry issued 0 txns; Key()="")
  ```

  Against a real cluster, the reporter of #22123 gets the same with a context canceled before the
  call.
- **Expected**: `Resign` documents only "lets a leader start a new election". An error return
  should leave the `Election` as it was, so that the caller can retry; the guard
  `CreateRevision(key) = rev` makes a retry safe (it cannot delete a newer incarnation of the key).
  The local state should be cleared only on a successful response (including one whose comparison
  failed, when the key is already gone).
- **How the proof handles it**: the proof states it. `Election.Resign.spec`'s error case
  (`Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Resign.lean:45`) is `⌜st.sess ≠ null ∧
  err ≠ nil⌝ ∗ electionState e s ⟨[], st.rev, null, st.hdr⟩`: the key and session cleared, and
  nothing about the key in etcd. Its no-op case (`:40`) then covers the retry. The proof
  (`Proof/go_etcd_io/etcd/client/v3/concurrency/Election__Resign.lean`, linked at
  `Proof/go_etcd_io/etcd/client/v3/concurrency/Link.lean:341`) is sorry-free; the spec is accurate
  but too weak to exclude the bug (class C-err). The stronger statement
  `election-key-accountable` (every error leaves the key accounted for in the `Election` or shows
  it gone from etcd), in `notes/bug-triage/etcd-21128.md`, fails on the pinned `Resign` exactly
  here.
- **Possible fixes**: clear `leaderKey`/`leaderSession` only when the transaction returns no error
  (#22124). `Campaign`'s calls to `Resign` on its failure paths then leave the state for the caller
  to retry.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#21128 against the `concurrency` specs (the
  `Resign` spec's error case); upstream as etcd-io/etcd#22123.
