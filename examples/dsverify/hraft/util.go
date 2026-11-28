// Copyright IBM Corp. 2013, 2025
// SPDX-License-Identifier: MPL-2.0

package raft

import (
	"fmt"
	"time"

	"github.com/goose-lang/primitive"
)

// randomTimeout returns a value that is between the minVal and 2x minVal.
func randomTimeout(minVal time.Duration) <-chan time.Time {
	if minVal == 0 {
		return nil
	}
	extra := time.Duration(primitive.RandomUint64() % uint64(minVal))
	return time.After(minVal + extra)
}

// min returns the minimum.
func min(a, b uint64) uint64 {
	if a <= b {
		return a
	}
	return b
}

// max returns the maximum.
func max(a, b uint64) uint64 {
	if a >= b {
		return a
	}
	return b
}

// generateUUID is used to generate a random UUID.
func generateUUID() string {
	buf := make([]byte, 16)
	for i := 0; i < 16; i++ {
		buf[i] = byte(primitive.RandomUint64())
	}

	return fmt.Sprintf("%08x-%04x-%04x-%04x-%12x",
		buf[0:4],
		buf[4:6],
		buf[6:8],
		buf[8:10],
		buf[10:16])
}

// asyncNotifyCh is used to do an async channel send
// to a single channel without blocking.
func asyncNotifyCh(ch chan struct{}) {
	select {
	case ch <- struct{}{}:
	default:
	}
}

// drainNotifyCh empties out a single-item notification channel without
// blocking, and returns whether it received anything.
func drainNotifyCh(ch chan struct{}) bool {
	select {
	case <-ch:
		return true
	default:
		return false
	}
}

// overrideNotifyBool is used to notify on a bool channel
// but override existing value if value is present.
// ch must be 1-item buffered channel.
//
// This method does not support multiple concurrent calls.
func overrideNotifyBool(ch chan bool, v bool) {
	select {
	case ch <- v:
		// value sent, all done
	case <-ch:
		// channel had an old value
		select {
		case ch <- v:
		default:
			panic("race: channel was sent concurrently")
		}
	}
}

// backoff is used to compute an exponential backoff
// duration. Base time is scaled by the current round,
// up to some maximum scale factor.
func backoff(base time.Duration, round, limit uint64) time.Duration {
	power := min(round, limit)
	for power > 2 {
		base *= 2
		power--
	}
	return base
}

// cappedExponentialBackoff computes the exponential backoff with an adjustable
// cap on the max timeout.
func cappedExponentialBackoff(base time.Duration, round, limit uint64, cap time.Duration) time.Duration {
	power := min(round, limit)
	for power > 2 {
		if base > cap {
			return cap
		}
		base *= 2
		power--
	}
	if base > cap {
		return cap
	}
	return base
}

// Needed for sorting []uint64, used to determine commitment
// sortUint64s sorts a in increasing order (insertion sort; upstream: sort.Sort on a uint64Slice).
func sortUint64s(a []uint64) {
	for i := 1; i < len(a); i++ {
		for j := i; j > 0 && a[j] < a[j-1]; j-- {
			a[j], a[j-1] = a[j-1], a[j]
		}
	}
}
