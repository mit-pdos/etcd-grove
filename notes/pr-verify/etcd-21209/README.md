# Probe & Reproduction Tests for `etcd-io/etcd#21209`

This directory contains the Go probe tests and test log for `etcd-io/etcd#21209` (`robustness: add Count and Keys to Kubernetes traffic generator`):

- [`keys_pr21209_probe_test.go`](keys_pr21209_probe_test.go):
  1. `TestPR21209_KeysBasicAndRevision`: Verifies that `Client.Keys` constructs a `WithRange(GetPrefixRangeEnd(prefix))`, `WithKeysOnly()`, `WithRev(opts.Revision)` `Get` request and populates `KeysResponse.{Keys, Count, Revision}` on success (or returns a zero `KeysResponse` and the error on failure).
  2. `TestPR21209_EmptyPrefixKeysVsCount`: Demonstrates that `Client.Count("", ...)` uses `clientv3.WithPrefix()` (which rewrites an empty prefix `""` to `Key="\x00", RangeEnd="\x00"`), whereas `Client.Keys("", ...)` uses `clientv3.WithRange(clientv3.GetPrefixRangeEnd(""))` (which leaves `Key=""` empty and sets `RangeEnd="\x00"`, causing `etcdserver`'s `checkRangeRequest` to reject the request with `rpctypes.ErrEmptyKey`).
  3. `TestPR21209_RecordingClientStripsWithCountOnly`: Demonstrates that in `tests/robustness/client/client.go:94-120`, `(*RecordingClient).Get` calls `c.Range(ctx, key, string(op.RangeBytes()), op.Rev(), op.Limit(), op.IsKeysOnly())`, which ignores `op.IsCountOnly()`. Consequently, when `kubernetesTraffic.Count` (added by PR `#21209`) calls `kc.Count(ctx, keyPrefix, CountOptions{})` on a `RecordingClient`, `WithCountOnly()` is silently stripped and a full `Range` (fetching all keys and values) is sent to etcd and recorded in Porcupine history.
- [`probe-test.log`](probe-test.log): Output of running `go test -v ./kubernetes -run 'TestPR21209'` in `/root/etcd-pr/etcd-21209/client/v3`.

## Running

```bash
cp notes/pr-verify/etcd-21209/keys_pr21209_probe_test.go /root/etcd-pr/etcd-21209/client/v3/kubernetes/
cd /root/etcd-pr/etcd-21209/client/v3 && go test -v ./kubernetes -run 'TestPR21209'
rm /root/etcd-pr/etcd-21209/client/v3/kubernetes/keys_pr21209_probe_test.go
```
