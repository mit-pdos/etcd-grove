# Reproduction & Probe Tests for `etcd-io/etcd#22617`

- `mutex_test.go`: Integration test `TestMutexLockKeyRecreated` (`tests/integration/clientv3/concurrency/mutex_test.go`) from `etcd-io/etcd#22617`.
- `mutex_recreated_head.log`: Output of running `TestMutexLockKeyRecreated` on `pr-etcd-22617-goose-lean` (`5860cea341762fa92eb143b7467ba59a3a6c64c9`, with `etcd-io/etcd#22617` applied), where `m2.Lock` returns `ErrSessionExpired` and the test passes (`PASS: TestMutexLockKeyRecreated`).
- `mutex_recreated_base.log`: Output of running `TestMutexLockKeyRecreated` on the base revision (`bc9c3868ced67e518fb2fecba44ce0fa70b7303b`, without `etcd-io/etcd#22617`), where `m2.Lock` returns `nil` while `m3` holds the lock (`Error: An error is expected but got nil`, `Messages: m2 locked while m3 holds the lock`).

## Running

```bash
cd /root/etcd-pr/etcd-22617/tests
go test -v -run '^TestMutexLockKeyRecreated$' ./integration/clientv3/concurrency
```
