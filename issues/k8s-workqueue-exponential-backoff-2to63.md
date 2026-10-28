---
upstream: unchecked
checked: 2026-10-27
links: []
---

# client-go's exponential failure rate limiter returns a negative delay when the backoff is exactly 2^63 ns

- **Status**: a bug (a wrong result), reachable only with a base delay that is a power of two
  nanoseconds (`time.Nanosecond`, `1024 * time.Nanosecond`, ...) and 64 - log2(base) consecutive
  failures of one item without `Forget`. Not reached by `DefaultTypedControllerRateLimiter` (5 ms)
  or `DefaultTypedItemBasedRateLimiter` (1 ms): their base delays are not powers of two, so the
  product is never exactly `2^63`.
- **Where**: `k8s.io/client-go/util/workqueue/default_rate_limiters.go` at the pinned
  `v0.0.0-20261021054439-569675c57fa3` (unchanged on kubernetes/kubernetes master `a7225301`,
  2026-10-26, line 125), `(*TypedItemExponentialFailureRateLimiter[T]).When`:

  ```go
  // The backoff is capped such that 'calculated' value never overflows.
  backoff := float64(r.baseDelay.Nanoseconds()) * math.Pow(2, float64(exp))
  if backoff > math.MaxInt64 {
      return r.maxDelay
  }
  calculated := time.Duration(backoff)
  ```

  `math.MaxInt64` converts to the `float64` `2^63` (it is not representable; the nearest is
  `2^63`). A `backoff` of exactly `2^63` is not `>` it, and `time.Duration(backoff)` converts a
  `float64` outside `int64`'s range: implementation-defined in Go ("if the value cannot be
  represented ... the result value is implementation-dependent"); on amd64 it is `math.MinInt64`.
  `calculated > r.maxDelay` is then false, and `When` returns `-2562047h47m16.854775808s`. The
  comment claims the cap makes the conversion safe; it is off by one at the boundary.
- **What happens** (Go test against the pin, fails on amd64):

  ```go
  func TestExponentialWhenAt2to63(t *testing.T) {
      r := workqueue.NewTypedItemExponentialFailureRateLimiter[string](time.Nanosecond, 1000*time.Second)
      var d time.Duration
      for i := 0; i <= 63; i++ { d = r.When("x") }
      if d < 0 { t.Errorf("When = %v, want %v", d, 1000*time.Second) }
      // When after 64 failures = -2562047h47m16.854775808s
  }
  ```

  A negative delay makes `AddRateLimited` (`AddAfter` with it) add the item at once instead of
  after `maxDelay`: the item is retried in a hot loop for that one failure (the next `When` has
  `exp = 64`, `backoff = 2^64 > 2^63`, and returns `maxDelay` again).
- **Expected**: `When` returns at most `maxDelay` and at least `0` (for a non-negative base
  delay), as the comment says.
- **How the proof handles it**: `TypedItemExponentialFailureRateLimiter.When`'s spec
  (`Spec/k8s_io/client_go/util/workqueue/TypedItemExponentialFailureRateLimiter__When.lean`) states
  only what holds for every base delay: it returns `maxDelay` or the conversion of the computed
  backoff, which the model's `float64`-to-`int64` conversion leaves uninterpreted
  (`EtcdGrove.Float64ToInt64Semantics`); it does not claim a non-negative result.
- **Possible fixes**: `if backoff >= math.MaxInt64` (the cap then also catches `2^63`; any
  `float64` below `2^63` converts exactly in range), or compare with `float64(r.maxDelay)` before
  converting.
- **Found**: 2026-10-27, specifying the work queue's rate limiters (the DaemonSet plan's phase 2):
  the `float64`-to-`int64` conversion has no specified result out of range, so the spec could not
  state the comment's bound.
