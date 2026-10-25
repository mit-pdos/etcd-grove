# Reproduction Tests and Logs for `etcd-io/etcd#22658`

This directory contains standalone reproduction tests and test output logs for the verification of [`etcd-io/etcd#22658`](https://github.com/etcd-io/etcd/pull/22658) (`client/v3: fix nil panic in SetEndpoints on NewCtxClient`, head `8265a260b40ac680525800e84ae3ad262e52f07c`).

## Files

- [`repro_test.go`](./repro_test.go): Standalone Go test suite verifying the behavior of `Client.SetEndpoints` and `NewCtxClient` before and after PR `#22658`:
  1. `TestBeforePR22658_SetEndpointsOnNewCtxClientPanics`: Reproduces the pre-PR `#22658` `SIGSEGV` nil-pointer dereference when calling `SetEndpoints` on a client constructed by `NewCtxClient` (where `c.resolver == nil`).
  2. `TestAfterPR22658_SetEndpointsOnNewCtxClientSucceeds`: Verifies that with PR `#22658`'s `if c.resolver != nil` guard, `SetEndpoints` on a `NewCtxClient` succeeds and updates `c.endpoints` (returned by `c.Endpoints()`).
  3. `TestAfterPR22658_SetEndpointsWithNonNilResolverUpdatesBoth`: Verifies that when `c.resolver != nil` (as constructed by `clientv3.New` / `newClient`), `SetEndpoints` updates both `c.endpoints` and `c.resolver.endpoints`.
- [`repro_test.log`](./repro_test.log): Output from running `go test -v ./...`.

## Running

```bash
cd notes/pr-verify/etcd-22658
go test -v ./...
```
