---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#13682 pr merged: related, not this bug (the unchecked prefix assertion in tokenSimple.assign, nonissues/etcd-auth-simple-token-assign-prefix-panic.md)
blocks-proof: yes
---

# auth: two internal root tokens with the same random prefix make the member panic

With auth enabled and the simple token provider (the default `--auth-token`), every lease-revocation
batch of the leader and every health check (`/health`, `/livez`, `/readyz`:
`api/etcdhttp/health.go:222,434`) asks `WithRoot` for a root token `prefix.0`, with a fresh random 16-letter
prefix and the index `0`. If a prefix repeats while the earlier token is still in the provider's map
(its TTL, 300 seconds by default), `assignSimpleTokenToUser` calls `lg.Panic("failed to assign
already-used simple token to a user")` and the member exits.

**Why not an issue:** no test; found by code reading (the auth store's specs, 2026-11-09). The
probability is negligible (52^-16 per pair of root tokens alive together; health probes every few
seconds keep about a hundred alive), but it is not zero: no
code excludes it.

## Proof

yes: a sound spec of `WithRoot` with the simple provider cannot exclude the panic; the spec takes
the premise `rootTokOk` (`Spec/go_etcd_io/etcd/server/v3/auth/authStore__WithRoot.lean`), which the
no-op and JWT providers give and the simple one does not. A fix on the fork, or a probabilistic
premise, is the user's decision (`notes/specs-only/batch-3d.md`).

## Notes

A fix: in `assignSimpleTokenToUser`, return an error (or regenerate the prefix) for a token already
in the map instead of panicking; `WithRoot` already handles an `assign` error by logging and
returning the context unchanged.
