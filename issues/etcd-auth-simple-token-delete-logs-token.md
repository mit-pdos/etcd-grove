---
upstream: unchecked
links:
  - etcd-io/etcd#20934 pr merged: logs token fingerprints instead of tokens (commit 7cc7eaaf6); misses this one
---

# The simple-token keeper logs a deleted token in plaintext

**Status**: a minor leftover of etcd-io/etcd#20934, found while verifying etcd-io/etcd#19775
(`notes/pr-verify/etcd-19775.md`). It is not in the verified code: `simple_token.go` is translated
names-only.

**Where**: `server/auth/simple_token.go:175` at the pinned `09669450f` and on upstream `main`.
The token keeper's `delf` callback, which `simpleTokenTTLKeeper.run` calls when a token expires, logs
at Debug level:
`t.lg.Debug("deleted a simple token", zap.String("user-name", username), zap.String("token", tk))`.

**What happens**: with debug logging on, the whole simple token is written to the log. The token has
expired at that point (`invalidateUser` deletes from the map itself, without the callback), so the
exposure is small. After #20934, every other auth log line in the package logs
`token-fingerprint` (`redactToken`).

**Expected**: the same as #20934's other lines: `zap.String("token-fingerprint", redactToken(tk))`.
