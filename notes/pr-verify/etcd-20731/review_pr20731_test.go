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

func revClient(n int) *Client {
	eps := make([]string, n)
	for i := range eps {
		eps[i] = "127.0.0.1:2379"
	}
	c := &Client{epMu: new(sync.RWMutex), endpoints: eps}
	c.lg.Store(zap.NewNop())
	return c
}

// R1: the jitter is applied after the cap, so the wait exceeds BackoffMaxWaitBetween
// ("the max wait time before retrying") by up to jitterFraction.
func TestReviewJitterExceedsMax(t *testing.T) {
	c := revClient(1)
	max := 5 * time.Second
	bf := c.roundRobinQuorumBackoff(25*time.Millisecond, 0.10, 2.0, max)
	over, hi := 0, time.Duration(0)
	for i := 0; i < 1000; i++ {
		d := bf(20)
		if d > max {
			over++
		}
		if d > hi {
			hi = d
		}
	}
	t.Logf("capped backoff above max %v: %d/1000, highest %v", max, over, hi)
}

// R2: the overflow of finding 3 is not limited to MaxInt64: any max above
// 2^63/(1+jitter) (~8.38e18ns with the default jitter) gives out-of-range
// conversions in jitterUp for the upper jitter half.
func TestReviewLargeMaxJitterOverflow(t *testing.T) {
	c := revClient(1)
	max := time.Duration(9e18)
	bf := c.roundRobinQuorumBackoff(25*time.Millisecond, 0.10, 2.0, max)
	neg := 0
	for i := 0; i < 1000; i++ {
		if bf(60) <= 0 {
			neg++
		}
	}
	t.Logf("max=9e18ns (< MaxInt64), jitter 0.1: %d/1000 capped backoffs <= 0; expBackoff=%d", neg, int64(expBackoff(60, 2.0, 25*time.Millisecond, max)))
}

// R3: exponent in (0,1) with the stream path's max-uint retries (Snapshot):
// the wait reaches 0 and the client retries with no backoff at all.
func TestReviewSmallExponentZeroWait(t *testing.T) {
	c := revClient(1)
	bf := c.roundRobinQuorumBackoff(25*time.Millisecond, 0.10, 0.5, 5*time.Second)
	for _, a := range []uint{1, 10, 25, 30, 40} {
		t.Logf("exponent 0.5, attempt %d: %v", a, bf(a))
	}
}

// R4: extreme but accepted float inputs: +Inf exponent, +Inf jitter, MaxFloat64.
func TestReviewInfInputs(t *testing.T) {
	c := revClient(1)
	t.Logf("exp=+Inf: %v", c.roundRobinQuorumBackoff(25*time.Millisecond, 0, math.Inf(1), 5*time.Second)(1))
	t.Logf("exp=MaxFloat64: %v", c.roundRobinQuorumBackoff(25*time.Millisecond, 0, math.MaxFloat64, 5*time.Second)(1))
	neg := 0
	bf := c.roundRobinQuorumBackoff(25*time.Millisecond, math.Inf(1), 1.0, 5*time.Second)
	for i := 0; i < 100; i++ {
		if bf(1) <= 0 {
			neg++
		}
	}
	t.Logf("jitter=+Inf: %d/100 <= 0 (pre-existing: jitterUp is unchanged)", neg)
}

// R5: endpoints changing between attempts of one retry sequence: the quorum
// changes, so generations jump or repeat and backoffs are skipped. No panic.
func TestReviewQuorumChange(t *testing.T) {
	c := revClient(1)
	bf := c.roundRobinQuorumBackoff(10*time.Millisecond, 0, 2.0, 5*time.Second)
	var seq []time.Duration
	for a := uint(1); a <= 8; a++ {
		if a == 4 {
			c.endpoints = make([]string, 7) // quorum 1 -> 4
		}
		seq = append(seq, bf(a))
	}
	t.Logf("1 endpoint, then 7 from attempt 4: %v", seq)
	c.endpoints = nil
	t.Logf("0 endpoints (quorum 1), attempt 3: %v", bf(3))
}

// R6 (pre-existing, not the PR): a nil logger (c.WithLogger(nil), public)
// makes the closure panic in Debug.
func TestReviewNilLoggerPanics(t *testing.T) {
	c := revClient(1)
	c.WithLogger(nil)
	defer func() { t.Logf("recovered: %v", recover()) }()
	c.roundRobinQuorumBackoff(time.Millisecond, 0, 1.0, time.Second)(1)
}
