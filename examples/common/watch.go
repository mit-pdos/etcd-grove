package common

import (
	"context"
	"sync"

	"github.com/goose-lang/primitive"

	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// The watch workload's shared part (watchkv's, which cachekv and linkv3p's MainWatch repeated):
// writers putting random keys under a prefix, each successful Put logged, a watch read until it
// has reported every successful Put, and the check that it reported exactly the writes.

// A KV is a key and a value.
type KV struct {
	Key string
	Val string
}

// A PutRec is a Put that returned no error: its reply's header revision, its key and value.
type PutRec struct {
	Rev int64
	Key string
	Val string
}

// An Event is a watched event: its revision (its key-value's mod revision), key, value, and
// whether it is a put.
type Event struct {
	Rev int64
	Key string
	Val string
	Put bool
}

// The writers' log: every Put that returned no error.
type Writes struct {
	Mu sync.Mutex
	Ok []PutRec
}

// Gen picks a key of keys and a value, from a small set.
func Gen(keys []string) KV {
	vals := []string{"a", "b", "c", "d"}
	n := primitive.RandomUint64()
	k := keys[n%uint64(len(keys))]
	n = n / uint64(len(keys))
	return KV{Key: k, Val: vals[n%uint64(len(vals))]}
}

// GenAll picks n Puts (Gen of keys): the writers' Puts, writer i's at [i*nops, (i+1)*nops).
func GenAll(n int, keys []string) []KV {
	var all []KV
	for i := 0; i < n; i++ {
		all = append(all, Gen(keys))
	}
	return all
}

// Writer does the Puts tried[lo:hi] through cli, in order, logging in w each that returned no
// error, with its reply's revision.
func Writer(cli *clientv3.Client, w *Writes, tried []KV, lo int, hi int) {
	ctx := context.Background()
	for k := lo; k < hi; k++ {
		p := tried[k]
		resp, err := cli.Put(ctx, p.Key, p.Val)
		if err == nil {
			w.Mu.Lock()
			w.Ok = append(w.Ok, PutRec{Rev: resp.Header.Revision, Key: p.Key, Val: p.Val})
			w.Mu.Unlock()
		}
	}
}

// MaxRev is the highest revision of the successful Puts oks (0 if there is none).
func MaxRev(oks []PutRec) int64 {
	var m int64
	for _, p := range oks {
		if p.Rev > m {
			m = p.Rev
		}
	}
	return m
}

// Collect reads the watch channel wch until an event at revision upTo or above (at once if
// upTo is 0), returning the events read and true; false if the channel closed, or a response
// reported an error, before.
func Collect(wch clientv3.WatchChan, upTo int64) ([]Event, bool) {
	var evs []Event
	var last int64 // the last event's revision
	if upTo == 0 {
		return evs, true
	}
	for wresp := range wch {
		if wresp.Err() != nil {
			return evs, false
		}
		// Gooseable: mvccpb.Event rather than its alias clientv3.Event (the same type): Goose does
		// not resolve a type alias when it selects a field through a pointer.
		var es []*mvccpb.Event = wresp.Events
		for _, e := range es {
			evs = append(evs, Event{Rev: e.Kv.ModRevision, Key: string(e.Kv.Key),
				Val: string(e.Kv.Value), Put: e.Type == mvccpb.Event_PUT})
			last = e.Kv.ModRevision
		}
		if len(evs) > 0 && last >= upTo {
			return evs, true
		}
	}
	return evs, false
}

// Attempted reports whether (key, val) is one of the Puts tried.
func Attempted(tried []KV, key string, val string) bool {
	for _, p := range tried {
		if p.Key == key && p.Val == val {
			return true
		}
	}
	return false
}

// Check panics unless the events evs are the writes: all puts, at strictly increasing revisions,
// gap-free from revision 2, each a put some writer attempted (tried), and every successful Put
// (oks) the event at its revision with its key and value. Its panic messages start with name and
// call a write put.
func Check(name string, put string, evs []Event, tried []KV, oks []PutRec) {
	var prev int64 // the previous event's revision
	for i, e := range evs {
		if !e.Put {
			panic(name + ": a watched event is not a put")
		}
		if i > 0 && e.Rev <= prev {
			panic(name + ": the watched revisions do not increase")
		}
		if e.Rev != int64(i)+2 {
			panic(name + ": the watched revisions are not those from 2 on, without a gap")
		}
		if !Attempted(tried, e.Key, e.Val) {
			panic(name + ": a watched put no writer attempted")
		}
		prev = e.Rev
	}
	for _, p := range oks {
		i := p.Rev - 2
		if i < 0 || i >= int64(len(evs)) {
			panic(name + ": a successful " + put + "'s revision was not watched")
		}
		e := evs[i]
		if e.Key != p.Key || e.Val != p.Val {
			panic(name + ": the event at a successful " + put + "'s revision is not that " + put)
		}
	}
}
