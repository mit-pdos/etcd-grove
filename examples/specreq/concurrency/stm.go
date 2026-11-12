package concurrency

import (
	"context"
	"errors"
	"strconv"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
)

// REQ concurrency/stm-transfer: a transfer between two accounts committed through the STM keeps
// their sum: the committed attempt read both balances at the state it was applied to
// (serializability), so the caller's invariant "a + b = total" is preserved by every commit; the
// closure's captured variables reflect the committed attempt.
// Users: etcd's tests (example_stm_test.go: the bank transfer, the default level).
// Assumes: the owner's invariant holds "a and b hold decimal integers summing to total" and is the
// relation T given to NewSTM: it is stable under stmEff (any committed attempt whose writes are
// a transfer computed from its reads, applied where its reads agree), and no other principal
// writes a or b; time-free: a and b on no lease.
// Specs: NewSTM.spec (applyOk: the closure's Get, Put through stmAt_methods), Client.Get.spec.
func ReqSTMTransfer(cli *clientv3.Client, a, b string, amount int) {
	var seenA, seenB int
	_, err := concurrency.NewSTM(cli, func(s concurrency.STM) error {
		x, _ := strconv.Atoi(s.Get(a))
		y, _ := strconv.Atoi(s.Get(b))
		seenA, seenB = x, y
		if x < amount {
			return errors.New("insufficient")
		}
		s.Put(a, strconv.Itoa(x-amount))
		s.Put(b, strconv.Itoa(y+amount))
		return nil
	})
	if err != nil {
		return
	}
	if seenA < amount {
		panic("stm: committed an attempt the closure refused")
	}
	_ = seenB
}

// REQ concurrency/stm-levels: every isolation level runs and commits (or errs) without a panic;
// the deprecated constructors are the levels with an abort context.
// Users: etcd's tests (stm tests per level), tools/benchmark (not in the pinned sources).
// Assumes: none.
// Specs: NewSTM.spec, WithIsolation.spec, WithAbortContext.spec, NewSTMRepeatable.spec,
// NewSTMSerializable.spec, NewSTMReadCommitted.spec.
func ReqSTMLevels(ctx context.Context, cli *clientv3.Client, k string) {
	apply := func(s concurrency.STM) error {
		v := s.Get(k)
		s.Put(k, v+"x")
		if s.Get(k) != v+"x" {
			panic("stm: a write not read back")
		}
		return nil
	}
	for _, iso := range []concurrency.Isolation{concurrency.SerializableSnapshot,
		concurrency.Serializable, concurrency.RepeatableReads, concurrency.ReadCommitted} {
		_, _ = concurrency.NewSTM(cli, apply, concurrency.WithIsolation(iso),
			concurrency.WithAbortContext(ctx))
	}
	_, _ = concurrency.NewSTMRepeatable(ctx, cli, apply)
	_, _ = concurrency.NewSTMSerializable(ctx, cli, apply)
	_, _ = concurrency.NewSTMReadCommitted(ctx, cli, apply)
}

// REQ concurrency/stm-repeatable: within an attempt, a key read twice reads the same (the read
// set), and Rev agrees with the read.
// Users: etcd's tests (stm tests), any closure reading a key twice.
// Assumes: none.
// Specs: NewSTM.spec, stmAt_methods (GetPost, RevPost).
func ReqSTMRepeatable(cli *clientv3.Client, k string) {
	_, _ = concurrency.NewSTM(cli, func(s concurrency.STM) error {
		v1 := s.Get(k)
		r1 := s.Rev(k)
		if s.Get(k) != v1 || s.Rev(k) != r1 {
			panic("stm: a read changed within the attempt")
		}
		if v1 != "" && r1 == 0 {
			panic("stm: a present key without a revision")
		}
		return nil
	})
}

// REQ concurrency/stm-prefetch: WithPrefetch's keys are read before the closure, at no cost to its
// meaning.
// Users: etcd's tests (stm tests with WithPrefetch).
// Assumes: none.
// Specs: NewSTM.spec, WithPrefetch.spec.
func ReqSTMPrefetch(cli *clientv3.Client, k1, k2 string) {
	_, _ = concurrency.NewSTM(cli, func(s concurrency.STM) error {
		s.Put(k1, s.Get(k2))
		return nil
	}, concurrency.WithPrefetch(k1, k2))
}

// REQ concurrency/stm-abort: a closure's error is NewSTM's, with no response; nothing committed.
// Users: etcd's tests (stm abort tests).
// Assumes: none.
// Specs: NewSTM.spec (stmResult's error case: the closure's or a request's error).
func ReqSTMAbort(cli *clientv3.Client, k string) {
	errAbort := errors.New("abort")
	resp, err := concurrency.NewSTM(cli, func(s concurrency.STM) error {
		s.Put(k, "x")
		return errAbort
	})
	if err == nil {
		panic("stm: the closure's error lost")
	}
	if resp != nil {
		panic("stm: a response with an error")
	}
}
