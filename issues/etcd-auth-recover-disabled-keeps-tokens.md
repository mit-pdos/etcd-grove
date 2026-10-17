---
upstream: unchecked
checked: 2026-10-17
links: []
---

# Recover with auth disabled leaves the simple tokens valid

- **Status**: a bug (pre-existing; found while verifying PR etcd-io/etcd#22338, which does not
  touch it). Simple tokens issued before an `AuthDisable` survive on a member that learns of the
  disable from a snapshot, and are accepted again there after the next `AuthEnable`.
- **Where**: `server/auth/store.go:396-413` (`authStore.Recover`) at the pinned fork revision
  `09669450f` (identical on upstream `main` `b25719d10`):

  ```go
  as.enabledMu.Lock()
  as.enabled = enabled
  if enabled {
      as.tokenProvider.enable()
  }
  as.enabledMu.Unlock()
  ```

  `AuthDisable` (`store.go:301-322`) calls `as.tokenProvider.disable()`, which drops every simple
  token and stops the TTL keeper. `Recover` (the server's snapshot restore) sets `enabled` from
  the snapshot's backend but, when that says disabled, does not call `disable()`.
- **What happens**: a member that was behind when `AuthDisable` was applied and catches up through
  a snapshot keeps its in-memory tokens table and keeper. A later `AuthEnable` calls `enable()`,
  which returns at once because the keeper is still set, so the tokens issued before the disable
  are valid again on that member (until their TTL; with a long `--auth-token-ttl`, indefinitely),
  while the members that applied `AuthDisable` reject them. Reproduction
  (`notes/pr-verify/etcd-22338/server/auth/recover_disabled_tokens_test.go`, log
  `notes/pr-verify/etcd-22338/recover-disabled-tokens.log`): authenticate, `Recover` from a
  backend with auth disabled, `AuthEnable`; the old token's `info` is `ok`. The test fails at the
  pinned revision. With PR etcd#22338 the token-count gauge also stays at the old count.
- **Expected**: the disabled state after `Recover` is the same as after `AuthDisable`: no simple
  token issued before it is valid after a later enable.
- **How the proof handles it**: `Recover` is not translated with bodies (`auth.toml`); the
  provider's specs (`Spec/go_etcd_io/etcd/server/v3/auth/tokenSimple__*.lean`, branch
  `pr-verify/etcd-22338`) are of `enable`/`disable` alone, and `disable`'s postcondition (no token
  allowed) holds only for callers that call it.
- **Possible fixes**: in `Recover`, `else { as.tokenProvider.disable() }` (under `enabledMu`, as
  `AuthDisable` does).
- **Found**: 2026-10-17, by the reviewer of the pr-verify/etcd-22338 proofs (the provider's
  admin discipline: who calls `enable`/`disable`).
