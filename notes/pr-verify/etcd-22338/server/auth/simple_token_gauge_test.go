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

package auth

import (
	"context"
	"testing"
	"time"

	"github.com/prometheus/client_golang/prometheus/testutil"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"go.uber.org/zap/zaptest/observer"
)

func assignN(t *testing.T, tp *tokenSimple, user string, from, n int) {
	t.Helper()
	for i := from; i < from+n; i++ {
		ctx := context.WithValue(context.WithValue(t.Context(), AuthenticateParamIndex{}, uint64(i)),
			AuthenticateParamSimpleTokenPrefix{}, "prefix")
		if _, err := tp.assign(ctx, user, 0); err != nil {
			t.Fatal(err)
		}
	}
}

func gauge() int { return int(testutil.ToFloat64(simpleTokenGauge)) }

func tokenCount(tp *tokenSimple) int {
	tp.simpleTokensMu.Lock()
	defer tp.simpleTokensMu.Unlock()
	return len(tp.simpleTokens)
}

// TestSimpleTokenGaugeTracksCount: the gauge follows the number of tokens through assign,
// invalidateUser, expiry and disable.
func TestSimpleTokenGaugeTracksCount(t *testing.T) {
	oldRes := simpleTokenTTLResolution
	simpleTokenTTLResolution = 10 * time.Millisecond
	defer func() { simpleTokenTTLResolution = oldRes }()

	tp := newTokenProviderSimple(zap.NewNop(), dummyIndexWaiter, 200*time.Millisecond)
	tp.enable()
	assignN(t, tp, "u1", 1, 3)
	assignN(t, tp, "u2", 4, 2)
	if g, n := gauge(), tokenCount(tp); g != 5 || n != 5 {
		t.Fatalf("after 5 assigns: gauge %d, tokens %d", g, n)
	}
	tp.invalidateUser("u1")
	if g, n := gauge(), tokenCount(tp); g != 2 || n != 2 {
		t.Fatalf("after invalidating u1: gauge %d, tokens %d", g, n)
	}
	deadline := time.Now().Add(5 * time.Second)
	for tokenCount(tp) != 0 && time.Now().Before(deadline) {
		time.Sleep(10 * time.Millisecond)
	}
	if g, n := gauge(), tokenCount(tp); g != 0 || n != 0 {
		t.Fatalf("after expiry: gauge %d, tokens %d", g, n)
	}
	assignN(t, tp, "u3", 10, 4)
	tp.disable()
	if g := gauge(); g != 0 {
		t.Fatalf("after disable: gauge %d", g)
	}
}

// TestSimpleTokenGaugeSharedAcrossProviders: the gauge is one per process, so two providers
// in one process (several members of an embedded or integration-test cluster) overwrite each
// other's value: every TTL tick of each provider sets it to that provider's own count.
func TestSimpleTokenGaugeSharedAcrossProviders(t *testing.T) {
	oldRes := simpleTokenTTLResolution
	simpleTokenTTLResolution = 10 * time.Millisecond
	defer func() { simpleTokenTTLResolution = oldRes }()

	a := newTokenProviderSimple(zap.NewNop(), dummyIndexWaiter, time.Hour)
	b := newTokenProviderSimple(zap.NewNop(), dummyIndexWaiter, time.Hour)
	a.enable()
	defer a.disable()
	b.enable()
	assignN(t, a, "u", 1, 3)
	assignN(t, b, "u", 1, 1)
	seen := map[int]bool{}
	for i := 0; i < 200; i++ {
		seen[gauge()] = true
		time.Sleep(time.Millisecond)
	}
	t.Logf("gauge values seen with a=3 and b=1 tokens: %v", seen)
	if !seen[3] || !seen[1] {
		t.Errorf("expected the gauge to alternate between 3 and 1, saw %v", seen)
	}
	b.disable() // a still holds 3 tokens
	t.Logf("right after b.disable(): gauge %d, a's tokens %d", gauge(), tokenCount(a))
}

// TestSimpleTokenWarnAtEveryCrossing: the warning is logged each time the count reaches a
// multiple of 10000, also when it goes back to the same multiple after a deletion.
func TestSimpleTokenWarnAtEveryCrossing(t *testing.T) {
	core, logs := observer.New(zapcore.WarnLevel)
	tp := newTokenProviderSimple(zap.New(core), dummyIndexWaiter, time.Hour)
	tp.enable()
	defer tp.disable()
	assignN(t, tp, "bulk", 1, simpleTokenCountWarnThreshold-1)
	assignN(t, tp, "last", simpleTokenCountWarnThreshold, 1)
	first := logs.FilterMessage("high number of simple tokens stored in memory").Len()
	for i := 0; i < 5; i++ {
		tp.invalidateUser("last")
		assignN(t, tp, "last", simpleTokenCountWarnThreshold+1+i, 1)
	}
	total := logs.FilterMessage("high number of simple tokens stored in memory").Len()
	t.Logf("warnings: %d at the first crossing, %d after 5 delete/add cycles at the threshold", first, total)
	if total != first+5 {
		t.Errorf("expected %d warnings, got %d", first+5, total)
	}
}
