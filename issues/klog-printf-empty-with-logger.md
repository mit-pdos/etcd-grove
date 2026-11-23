---
upstream: none
checked: 2026-11-23
links:
  - kubernetes/klog#272 pr merged: the same panic in `Info("")`, fixed there for the print path only
blocks-proof: no
---
# klog: Infof, Warningf and Errorf panic on an empty message when a logger is set

With a `logr.Logger` installed by `klog.SetLogger` (without the `WriteKlogBuffer` option), any
printf-style call whose formatted message is empty, such as `klog.Infof("")`,
`klog.Errorf("%s", "")` or `klog.V(2).Infof("")`, panics with `index out of range [-1]` instead of
logging an empty line.

**Expected:** `Infof("")` should log as `Info("")` does, which kubernetes/klog#272 fixed for the same
configuration ("fixed empty info log panic").

**Impact:** any program that routes klog through a logr backend (`klog.SetLogger`, as Kubernetes
components using contextual logging do) and logs a printf-style message that can be empty, for
example `klog.Errorf("%v", err)` of an error whose `Error()` is `""`. The process crashes on the
log call. With klog's default configuration (no logger set) the header keeps the buffer non-empty
and nothing panics, except with `-skip_headers`. All releases since #272 (v2.50.0); found at
v2.140.0.

**Reproduction:** `TestPrintfEmptyWithLogger` in
[`issues/klog-printf-empty-with-logger/printf_empty_test.go`](klog-printf-empty-with-logger/printf_empty_test.go),
copied into the repository root at kubernetes/klog@8edf7b7bd0ce661a7e9283e0d1f52ec358d12469
(2026-11-18), go1.27.3:

```
$ go test . -run TestPrintfEmptyWithLogger
--- FAIL: TestPrintfEmptyWithLogger (0.00s)
    --- FAIL: TestPrintfEmptyWithLogger/Infof (0.00s)
        printf_empty_test.go:26: Infof panicked: runtime error: index out of range [-1]
    --- FAIL: TestPrintfEmptyWithLogger/Warningf (0.00s)
        printf_empty_test.go:26: Warningf panicked: runtime error: index out of range [-1]
    --- FAIL: TestPrintfEmptyWithLogger/Errorf (0.00s)
        printf_empty_test.go:26: Errorf panicked: runtime error: index out of range [-1]
    --- FAIL: TestPrintfEmptyWithLogger/V.Infof (0.00s)
        printf_empty_test.go:26: V.Infof panicked: runtime error: index out of range [-1]
FAIL
```

**Cause:** when a logger without `writeKlogBuffer` is set, `printfDepth` replaces the header
buffer by an empty one, formats into it, then reads its last byte unguarded,
`buf.Bytes()[buf.Len()-1]`
([klog.go#L781](https://github.com/kubernetes/klog/blob/8edf7b7bd0ce661a7e9283e0d1f52ec358d12469/klog.go#L781));
`printWithFileLine` does the same
([klog.go#L803](https://github.com/kubernetes/klog/blob/8edf7b7bd0ce661a7e9283e0d1f52ec358d12469/klog.go#L803)).
#272 added the `buf.Len() == 0 ||` guard to `printWithInfos` only
([klog.go#L754](https://github.com/kubernetes/klog/blob/8edf7b7bd0ce661a7e9283e0d1f52ec358d12469/klog.go#L754)).

## Proof

no: the verified Kubernetes code sets no klog logger and its formats are non-empty; klog's package
fact (`klogInit`, `Proof/k8s_io/apiserver/pkg/storage/etcd3/Base.lean`) has `logging.logger` `nil`.

## Fix

Add the same `buf.Len() == 0 ||` guard at the two places (not yet on a branch).
