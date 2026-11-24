/*
 *
 * Copyright 2026 the etcd-grove authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 */

package grpc

// MODEL: the model's choice points. These two functions are the model's only nondeterminism, and
// the only declarations of the package with a hand-written GooseLang body (trusted: any boolean,
// any index below n; so the model has every behavior on either side of a choice). In Go they
// take the common side (false, 0), so that a real run behaves as grpc-go usually does, unless the
// environment variable GRPC_MODEL_CHOOSE is "random" when the program starts: then each choice is
// random (a test knob, to run the model's rare paths: refused streams, idleness, failures of a
// fail-fast pick, the code of a transport failure, which reported address is dialed).

import (
	"math/rand/v2"
	"os"
	"sync"
	"time"

	"google.golang.org/grpc/resolver"
)

var modelChooseRandom = os.Getenv("GRPC_MODEL_CHOOSE") == "random"

// notModelled is the value the model panics with where it does not model grpc-go's behavior
// (models/README.md: a model's panics outside its scope have a NotModelled method), so that a
// proof that the program does not panic shows it never gets there: TLS and transport credentials
// other than insecure, a service config other than round robin's, compression, stats handlers,
// binary logging, an InTapHandle, Server.ServeHTTP, a unix address with a custom dialer.
type notModelled string

// NotModelled marks the value as the models' panic.
func (notModelled) NotModelled() {}

// modelChoose is an arbitrary boolean.
func modelChoose() bool {
	if modelChooseRandom {
		return rand.IntN(2) == 0
	}
	return false
}

// modelChooseN is an arbitrary index below n (n > 0).
func modelChooseN(n int) int {
	if modelChooseRandom && n > 0 {
		return rand.IntN(n)
	}
	return 0
}

// modelChooseLength is an arbitrary non-negative length (trusted, as modelChooseN: its GooseLang
// body is any non-negative int): what the model reports where grpc-go reports a length of its
// HTTP/2 encoding the model does not have (a header block's HPACK-encoded size, stats.InHeader's
// WireLength). Its Go body is n (the model's own estimate), or random with GRPC_MODEL_CHOOSE=random.
func modelChooseLength(n int) int {
	if modelChooseRandom {
		return rand.IntN(1 << 16)
	}
	return n
}

// modelChooseAddr is the index of the address an attempt dials: an arbitrary index below
// len(addrs) (trusted, as modelChooseN: its GooseLang body is any index). Its Go body plays
// grpc-go's round_robin, so that a real run spreads its attempts as grpc-go does: in turn, over
// the addresses whose last connection attempt did not fail and none of whose attempts has hung
// for half a second (round_robin picks among READY subchannels), over all of them if none is
// such. With GRPC_MODEL_CHOOSE=random, any index.
func modelChooseAddr(p *modelPicks, addrs []resolver.Address) int {
	if modelChooseRandom {
		return rand.IntN(len(addrs))
	}
	p.mu.Lock()
	defer p.mu.Unlock()
	var good []int
	for i, a := range addrs {
		h := p.health[a.Addr]
		if h == nil || (!h.failed && (h.dialing == 0 || time.Since(h.dialStart) < 500*time.Millisecond)) {
			good = append(good, i)
		}
	}
	if len(good) == 0 {
		for i := range addrs {
			good = append(good, i)
		}
	}
	p.next++
	return good[p.next%len(good)]
}

// modelNoteDial records the start of a connection attempt to addr for modelChooseAddr's Go body,
// and returns what records its end (trusted: in GooseLang both do nothing).
func modelNoteDial(p *modelPicks, addr string) func(ok bool) {
	p.mu.Lock()
	if p.health == nil {
		p.health = make(map[string]*addrHealth)
	}
	h := p.health[addr]
	if h == nil {
		h = &addrHealth{}
		p.health[addr] = h
	}
	if h.dialing == 0 {
		h.dialStart = time.Now()
	}
	h.dialing++
	p.mu.Unlock()
	return func(ok bool) {
		p.mu.Lock()
		h.dialing--
		h.failed = !ok
		if h.dialing > 0 {
			h.dialStart = time.Now()
		}
		p.mu.Unlock()
	}
}

// modelPicks is modelChooseAddr's memory (Go only).
type modelPicks struct {
	mu     sync.Mutex
	next   int
	health map[string]*addrHealth
}

type addrHealth struct {
	failed    bool
	dialing   int
	dialStart time.Time
}
