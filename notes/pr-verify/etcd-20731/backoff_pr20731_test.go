// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package clientv3

import (
	"math"
	"sync"
	"testing"
	"time"

	"go.uber.org/zap"
)

// rrClient is a client with n endpoints and a nop logger: enough for
// roundRobinQuorumBackoff's closure (it reads c.Endpoints() and c.GetLogger()).
func rrClient(t *testing.T, n int) *Client {
	t.Helper()
	eps := make([]string, n)
	for i := range eps {
		eps[i] = "127.0.0.1:2379"
	}
	c := &Client{epMu: new(sync.RWMutex), endpoints: eps}
	c.lg.Store(zap.NewNop())
	return c
}

// With the default exponent (1.0, documented as disabling exponential backoff
// "for reverse compatibility") and the default max (5s), a BackoffWaitBetween
// above 5s is silently capped to 5s: before the PR the client waited
// BackoffWaitBetween. dialSetupOpts passes exactly these values when only
// BackoffWaitBetween is configured.
func TestPR20731DefaultExponentCapsLargeWaitBetween(t *testing.T) {
	c := rrClient(t, 1)
	wait := 10 * time.Second
	bf := c.roundRobinQuorumBackoff(wait, 0, defaultBackoffExponent, defaultBackoffMaxWaitBetween)
	got := bf(1)
	if got != wait {
		t.Errorf("BackoffWaitBetween=%v, defaults otherwise: backoff = %v, want %v (the pre-PR wait)", wait, got, wait)
	}
}

// The first backoff of a retry sequence is attempt 1 (waitRetryBackoff calls
// the backoff function only for attempt > 0), which is generation 1 with one
// endpoint: the first wait is waitBetween*exponent, never waitBetween.
func TestPR20731FirstBackoffIsGenerationOne(t *testing.T) {
	c := rrClient(t, 1)
	wait := 100 * time.Millisecond
	bf := c.roundRobinQuorumBackoff(wait, 0, 2.0, 5*time.Second)
	if got := bf(1); got != wait {
		t.Logf("first backoff = %v, not BackoffWaitBetween = %v", got, wait)
	}
	// with 3 endpoints, quorum 2: attempts 2, 4, 6 back off, generations 1, 2, 3
	c3 := rrClient(t, 3)
	bf3 := c3.roundRobinQuorumBackoff(wait, 0, 2.0, 5*time.Second)
	for _, a := range []uint{1, 2, 3, 4, 6} {
		t.Logf("3 endpoints, attempt %d: %v", a, bf3(a))
	}
}

// A BackoffMaxWaitBetween of math.MaxInt64 (a common "no cap" value) makes
// expBackoff return time.Duration(float64(2^63)) once the cap is reached, a
// conversion out of int64's range whose result is implementation-defined (on
// amd64, math.MinInt64): a negative wait, which waitRetryBackoff treats as no
// wait at all. The retries that should wait longest do not wait.
func TestPR20731HugeMaxWaitBetweenGivesNegativeBackoff(t *testing.T) {
	d := expBackoff(100, 2.0, 25*time.Millisecond, time.Duration(math.MaxInt64))
	if d <= 0 {
		t.Errorf("expBackoff(100, 2.0, 25ms, MaxInt64) = %v (%d), want a positive wait", d, int64(d))
	}
	c := rrClient(t, 1)
	bf := c.roundRobinQuorumBackoff(25*time.Millisecond, 0.10, 2.0, time.Duration(math.MaxInt64))
	neg := 0
	for a := uint(40); a < 100; a++ {
		if bf(a) <= 0 {
			neg++
		}
	}
	if neg > 0 {
		t.Errorf("%d of 60 capped backoffs are <= 0 (no wait)", neg)
	}
}

// An exponent in (0, 1) is accepted (dialSetupOpts only checks > 0) and makes
// the wait shrink with every round, down to 0.
func TestPR20731ExponentBelowOneShrinks(t *testing.T) {
	c := rrClient(t, 1)
	bf := c.roundRobinQuorumBackoff(100*time.Millisecond, 0, 0.5, 5*time.Second)
	if got := bf(10); got < 100*time.Millisecond {
		t.Logf("exponent 0.5, attempt 10: backoff = %v < BackoffWaitBetween", got)
	}
}
