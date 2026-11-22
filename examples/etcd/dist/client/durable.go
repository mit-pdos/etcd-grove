package client

import (
	"context"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// MaxDurable bounds the durable workload's Puts (restartN's keys: one byte after the prefix).
const MaxDurable = 256

// How many times, and how far apart, the durable workload tries its final Range (a liveness
// bound: the members may be down or cut off for a while).
const (
	durableTries = 30
	durablePause = time.Second
)

// durableKey and durableValue are the i-th Put's key and value (restartN's key and value, under
// durablePrefix): the keys distinct, in the order of i.
func durableKey(i int) string   { return durablePrefix + string([]byte{'k', byte(i)}) }
func durableValue(i int) string { return string([]byte{'v', byte(i)}) }

// RunDurable is the durable workload (restartN's check, rewritten over gRPC: restartN's Puts and
// Range go through a member's own API, in the process that runs it, and its check is exact; Lean:
// Workload.durable, review F12): n <= MaxDurable Puts of distinct keys under durablePrefix, one
// after the other, while members crash and restart (the test's, not the program's); then a
// linearizable Range of the prefix, tried until one returns. Panics unless every acknowledged
// Put's key is in it with its value at version 1, and every key in it is one whose Put was
// attempted (a Put that failed may have been applied: an unknown outcome), with that Put's value
// at version 1 (each key is put once; the client sends a Put at most once, so it is applied at
// most once). No revision check: other workloads write.
func RunDurable(eps []string, n int) Result {
	if n > MaxDurable {
		n = MaxDurable
	}
	cli, err := newClient(eps)
	if err != nil {
		return ended("durable: the client failed to connect")
	}
	defer cli.Close()
	acked := make([]bool, n)
	for i := 0; i < n; i++ {
		ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		_, err := cli.Put(ctx, durableKey(i), durableValue(i))
		cancel()
		acked[i] = err == nil
	}
	for t := 0; t < durableTries; t++ {
		ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		resp, err := cli.Get(ctx, durablePrefix, clientv3.WithPrefix())
		cancel()
		if err != nil {
			time.Sleep(durablePause)
			continue
		}
		seen := make([]bool, n)
		for _, kv := range resp.Kvs {
			i := -1
			for j := 0; j < n; j++ {
				if string(kv.Key) == durableKey(j) {
					i = j
				}
			}
			if i < 0 {
				panic("dist durable: the Range returned a key no Put attempted")
			}
			if string(kv.Value) != durableValue(i) || kv.Version != 1 {
				panic("dist durable: the Range returned a wrong pair")
			}
			seen[i] = true
		}
		for i := 0; i < n; i++ {
			if acked[i] && !seen[i] {
				panic("dist durable: an acknowledged Put is missing")
			}
		}
		return checked()
	}
	return ended("durable: no Range returned")
}
