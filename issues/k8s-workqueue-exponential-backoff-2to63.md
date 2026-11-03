---
upstream: none
checked: 2026-11-01
links: []
blocks-proof: no
---

# client-go: the exponential failure rate limiter returns a negative delay when the backoff reaches exactly 2^63 ns

`ItemExponentialFailureRateLimiter.When` returns `-2562047h47m16.854775808s` (`math.MinInt64`) on
amd64 instead of its maximum delay when the backoff is exactly `2^63` ns: with a base delay of
`time.Nanosecond`, after 64 consecutive failures of one item. `AddRateLimited` then re-adds the
item at once, for that one failure. It needs a base delay that is a power of two nanoseconds
(`1ns`, `1024ns`, ...) and `64 - log2(base)` failures without `Forget`.

**Expected:** `When` should return a delay between 0 and the limiter's `maxDelay`: the limiter
"does a simple baseDelay*2^<num-failures> limit"
([doc](https://github.com/kubernetes/kubernetes/blob/v1.37.2/staging/src/k8s.io/client-go/util/workqueue/default_rate_limiters.go#L82-L83)),
and its own comment says the backoff "is capped such that 'calculated' value never overflows".

**Impact:** small. Only limiters built with a power-of-two-nanosecond base delay reach it; client-go's
defaults (`DefaultTypedControllerRateLimiter`, 5 ms; `DefaultTypedItemBasedRateLimiter`, 1 ms) and
round base delays (milliseconds, seconds) are not powers of two, so their product is never exactly
`2^63`. When reached, one retry happens without delay; the next `When` returns `maxDelay` again.

**Reproduction:** `TestExponentialWhenAt2to63` in
[`issues/k8s-workqueue-exponential-backoff-2to63/backoff_test.go`](k8s-workqueue-exponential-backoff-2to63/backoff_test.go),
copied into `util/workqueue` of a writable copy of `k8s.io/client-go@v0.37.2` (Kubernetes v1.37.2,
the latest release, 2026-11-01), go1.27.3 linux/amd64:

```
$ GOWORK=off GOFLAGS=-mod=mod go test ./util/workqueue -run TestExponentialWhenAt2to63 -count=1 -v
=== RUN   TestExponentialWhenAt2to63
    backoff_test.go:19: When after 64 failures = -2562047h47m16.854775808s, want between 0 and 16m40s
--- FAIL: TestExponentialWhenAt2to63 (0.00s)
FAIL
```

**Cause:** [`When`](https://github.com/kubernetes/kubernetes/blob/v1.37.2/staging/src/k8s.io/client-go/util/workqueue/default_rate_limiters.go#L123-L133)
caps the backoff with `backoff > math.MaxInt64`, but `math.MaxInt64` as a `float64` is `2^63`, so a
backoff of exactly `2^63` passes; `time.Duration(backoff)` then converts a `float64` outside
`int64`'s range, which Go leaves implementation-defined (`math.MinInt64` on amd64), and the
negative result passes `calculated > r.maxDelay`.

## Proof

no: `TypedItemExponentialFailureRateLimiter.When`'s spec
(`Spec/k8s_io/client_go/util/workqueue/TypedItemExponentialFailureRateLimiter__When.lean`) claims
only `maxDelay` or the conversion of the computed backoff, which the model leaves uninterpreted out
of range; it does not claim a non-negative delay, and the DaemonSet controller uses the defaults.

## Fix

`if backoff >= math.MaxInt64` (every `float64` below `2^63` converts in range).
