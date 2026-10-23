# Not issues

Findings moved out of `issues/` on review (2026-10-23, `issues/INDEX-reviewed.md`): preconditions etcd
meets, behavior that is no guarantee etcd makes, and (parked, for now) documentation-only findings the
review skipped. Each file says why in a note after its front matter; the file is otherwise as it was,
in the format of [../README.md](../README.md). `etc/issues-status.py` reads only `issues/*.md`, so these
are not in its listing. Move a file back to `issues/` if new evidence makes it an issue.

| Issue | Kind | Upstream | What to know |
|---|---|---|---|
| [election-campaign-key-check](election-campaign-key-check.md) | wrong result | not-filing | `Election.Campaign` returns nil without checking that its own key still exists. Not filed: equivalent to the session expiring right after `Campaign` returns, and fencing on the key's revision fails correctly. |
| [etcd-auth-newauthstore-nil-tp](etcd-auth-newauthstore-nil-tp.md) | precondition | none | `NewAuthStore` with a nil token provider panics on a backend where auth is enabled. Unreachable through `NewServer`; only tests pass nil, on fresh backends. |
| [etcd-auth-tls-info-assert](etcd-auth-tls-info-assert.md) | precondition | none | `AuthInfoFromTLS` asserts the peer's `AuthInfo` is a `credentials.TLSInfo` and panics otherwise. Unreachable in etcd's servers; fixed in the fork. |
| [etcd-bridge-blackhole-twice-panic](etcd-bridge-blackhole-twice-panic.md) | test code | none | The integration tests' bridge panics on a second `Blackhole` and leaves its mutex held, so later calls hang. A test helper's precondition (checked 2026-10-23 at `main` `3aaab3479`): no etcd test calls it twice. |
| [etcd-client-dialoptions-unary-interceptor](etcd-client-dialoptions-unary-interceptor.md) | docs | none | `Config.DialOptions` invites interceptors, but a `grpc.WithUnaryInterceptor` there replaces the client's own (retries included); only `WithChainUnaryInterceptor` keeps it. A cheap switch upstream would likely be accepted. |
| [etcd-featuregate-enabled-panic-undocumented](etcd-featuregate-enabled-panic-undocumented.md) | docs | none | The `FeatureGate.Enabled` interface omits the panic on an unregistered feature that its implementation documents. A one-line doc fix; unreachable from the server. |
| [etcd-index-compact-overlapping](etcd-index-compact-overlapping.md) | precondition | none | Two overlapping `treeIndex.Compact` passes can panic or delete a re-put key. Unreachable through the store, whose FIFO scheduler runs compactions one at a time. |
| [etcd-lessor-revoke-rd-unlocked](etcd-lessor-revoke-rd-unlocked.md) | precondition | none | `lessor.Revoke` reads `le.rd` without the lock that writes it. Unreachable in the server, where all of them run on the apply goroutine. |
