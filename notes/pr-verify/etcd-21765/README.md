# Reproduction & Probe Suite for `etcd-io/etcd#21765`

This directory contains executable Go tests and logs reproducing the findings identified during formal verification of `etcd-io/etcd#21765` (`[RFC] clientv3: add context-keyed channel pool`, commit `ca815f2104a34539bb95736b0aacad8e457389ae`).

## Files

- `channel_pool_verify_test.go`: Go test suite in package `clientv3` exercising Findings 1, 2a, 2b, 3, 4, and 6.
- `test.log`: Output of running `go test -v -count=1 -run 'TestVerify_' .` in `client/v3`.

## Running

Copy `channel_pool_verify_test.go` into `client/v3/` of the `pr-etcd-21765-goose-lean` worktree (`/root/etcd-pr/etcd-21765/client/v3`) and run:

```bash
GOTOOLCHAIN=go1.27.1 go test -v -count=1 -run 'TestVerify_' .
```
