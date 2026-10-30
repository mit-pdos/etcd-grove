---
upstream: unchecked
checked: 2026-10-30
links:
---

# auth: a serializable read can fail with "revision of auth store is old" while auth is disabled

- **Status**: a wrong result (a spurious error) in a less central configuration; not reproduced
  by a test yet. Found by reading the code; the model does not reach it (no TLS).
- **Where**: etcd fork pin (`etc/goose.py`, `.lake/etcd-fork` at `0df483bee`):
  - `EtcdServer.AuthInfoFromCtx` (`server/etcdserver/v3_server.go:1206-1216`): with no token and
    `ClientCertAuthEnabled`, it returns `AuthInfoFromTLS(ctx)`, whether auth is enabled or not.
  - `authStore.AuthInfoFromTLS` (`server/auth/store.go:1013-1054`): a verified client
    certificate with a common name gives `AuthInfo{Username: CN, Revision: as.Revision()}`
    (`:1024-1027`), a non-zero revision.
  - `EtcdServer.doSerialize` (`v3_server.go:1035-1057`): after `get()`, `ai.Revision != 0 &&
    ai.Revision != s.authStore.Revision()` returns `auth.ErrAuthOldRevision` (`:1053-1055`),
    without checking that auth is enabled (unlike `isOpPermitted`, `store.go:861-863`, which
    returns nil when auth is disabled).
  - The auth store's revision moves while auth is disabled: admin requests are permitted with auth
    off (`IsAdminPermitted`, `store.go:913-916`) and, e.g., `UserAdd` commits a new revision
    (`store.go:~461`, `commitRevision`).
- **What happens**: a server started with `--client-cert-auth` and auth disabled; a client with a
  certificate whose CN is set issues a serializable `Range` (served by `doSerialize`), while
  another client's `UserAdd` (or any auth-store write) commits between `AuthInfoFromTLS` and the
  revision check. The read fails with `etcdserver: revision of auth store is old`, though auth is
  off and the read was served. The client has no token, so its retry interceptor does not refresh
  one; the error reaches the caller.
- **Expected**: with auth disabled, no auth error (as `isOpPermitted` and `IsAdminPermitted` do).
- **How the proof handles it**: the modeled server has no TLS (`Spec/go_etcd_io/etcd/server/v3/
  etcdserver/api/v3rpc/Server.lean:32`), so `AuthInfoFromTLS` is never reached in the verified
  results; `isReqAuth` (`InvRequest.lean:1579-1589`) leaves `AuthInfoFromCtx`'s errors and TLS
  auth info unconstrained. Relevant to F-S2 part 2 (`notes/auth-mode-merge-plan.md`): an
  off-mode claim that no auth refusal happens is false of the Go with client-cert auth.
- **Possible fixes**: in `doSerialize`, skip the revision check when auth is disabled (or have
  `AuthInfoFromTLS` return revision 0 when auth is disabled).
- **Found**: 2026-10-30, by the spec review of F-S2 part 2's design
  (`fs2-part2-review1.md`, finding H2).
