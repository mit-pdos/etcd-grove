package dist

// The compactor workload: examples/k8s/compactor's MainPartition with its writer and its API
// servers on machines of their own. Machine 0 is the writer (compactor.writer's Writes Puts, of
// compactorcopy.WriteKeyShared: the cluster is the store workload's too, and the driver's writeKey
// is inside the store's keys); machines 1 to Servers are API servers with a compactor of their own (NewCompactor); the
// last machine is one API server process whose SharedServers storages share the process's
// compactor (StartCompactorPerEndpoint: sharing it is a process's, so they stay in one). Each API
// server's loop (its compactor's samples, Stop, the reads of compact_rev_key: the driver's check
// without its comparisons, compactorcopy.Sample) is one remote.Report call; the orchestrator
// (RunCompactor) makes check's comparisons on the reported values (compactorcopy.CheckLog) and
// panics if one fails, as the driver's API servers do. An API server that does not answer
// reports nothing, and nothing of it is checked: the driver's checks are each API server's own.

import (
	"sync"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/client"
	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/enc"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"

	comp "github.com/mit-pdos/etcd-grove/examples/k8s/dist/compactorcopy"
)

// CompactorMachines is the compactor workload's client machines: the writer, the API servers with
// their own compactor, and the process of the shared ones.
const CompactorMachines = 1 + comp.Servers + 1

// How long a call may take: the writer's whole loop (each Put within the request timeout); an API
// server's samples (ten intervals) and two reads.
const (
	writerAttempt    = time.Duration(comp.Writes)*etcdstart.RequestTimeout + 30*time.Second
	apiserverAttempt = 2*etcdstart.RequestTimeout + 30*time.Second
)

// compactorCodec is an API server's call: its machine's index in, its storages' logs out (one, or
// SharedServers on the shared process); the writer's: its index in, its number of Puts tried out.
func compactorCodec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte {
			e := &enc.Enc{}
			e.Int(in.(int))
			return e.B
		},
		DecIn: func(b []byte) (any, bool) {
			d := enc.NewDec(b)
			n := d.Int()
			return n, d.Done()
		},
		EncOut: func(out any) []byte {
			ls := out.([]comp.Log)
			e := &enc.Enc{}
			e.Int(len(ls))
			for _, l := range ls {
				e.Int(len(l.Samples))
				for _, s := range l.Samples {
					e.I64(s)
				}
				e.I64(l.Stopped)
				e.Bool(l.Get1)
				e.I64(l.Rev1)
				e.Bool(l.HasKey)
				e.Str(l.Value)
				e.Bool(l.Get2)
				e.I64(l.Rev2)
			}
			return e.B
		},
		DecOut: func(b []byte) (any, bool) {
			d := enc.NewDec(b)
			n := d.Int()
			var ls []comp.Log
			for i := 0; d.Ok && i < n; i++ {
				var l comp.Log
				k := d.Int()
				for j := 0; d.Ok && j < k; j++ {
					l.Samples = append(l.Samples, d.I64())
				}
				l.Stopped = d.I64()
				l.Get1 = d.Bool()
				l.Rev1 = d.I64()
				l.HasKey = d.Bool()
				l.Value = d.Str()
				l.Get2 = d.Bool()
				l.Rev2 = d.I64()
				ls = append(ls, l)
			}
			return ls, d.Done()
		},
	}
}

// CompactorNode is the compactor workload's client machine c at addr: its clients of eps made
// (trying until they are), it serves the orchestrator's one call (above). It never returns.
func CompactorNode(c int, addr string, eps []string) {
	var op func(any, any) any
	var d time.Duration
	switch {
	case c == 0:
		cli := client.ConnectRetry(eps)
		op = func(any, any) any {
			comp.WriterAt(cli, comp.WriteKeyShared)
			return []comp.Log{}
		}
		d = writerAttempt
	case c <= comp.Servers:
		cli := client.ConnectRetry(client.Rotate(eps, c))
		op = func(any, any) any {
			return []comp.Log{comp.Sample(cli, comp.NewOwn(cli))}
		}
		d = apiserverAttempt
	default:
		// one client per storage, of the same endpoints: StartCompactorPerEndpoint finds the
		// compactor the first one started (the driver's shared API servers dial the same bridges)
		var clis []*clientv3.Client
		for i := 0; i < comp.SharedServers; i++ {
			clis = append(clis, client.ConnectRetry(eps))
		}
		op = func(any, any) any {
			ls := make([]comp.Log, len(clis))
			var wg sync.WaitGroup
			for i, cli := range clis {
				wg.Add(1)
				go func() {
					ls[i] = comp.Sample(cli, comp.NewShared(cli))
					wg.Done()
				}()
			}
			wg.Wait()
			return ls
		}
		d = apiserverAttempt
	}
	remote.Serve(addr, nil, op, compactorCodec(), d)
}

// RunCompactor is the compactor workload's orchestrator: once its machines answer, it calls ready,
// then runs w.Rounds rounds (at least one; the driver's run is one): each starts the writer's loop
// (not awaited, as the driver's writer goroutine; a round's call waits behind the last one's on the
// writer's machine), calls every API server at once and checks each storage's log
// (compactorcopy.CheckLog: a failed comparison is a panic). Each round's API servers run the
// driver's apiserver afresh: a new compactor of their own, or the shared process's (the last
// Stop of a round removes it, and the next round's first storage starts another). Checked if an
// API server answered.
func RunCompactor(w Workload, addrs []string, ready func()) Result {
	if len(addrs) != CompactorMachines {
		return ended("not one machine per API server and writer")
	}
	if !client.AwaitAccept(addrs) {
		return ended("a client machine never answered")
	}
	ready()
	codec := compactorCodec()
	var ins []any
	for c := 1; c < CompactorMachines; c++ {
		ins = append(ins, c)
	}
	rounds := max(w.Rounds, 1)
	answered, logs := 0, 0
	for k := 0; k < rounds; k++ {
		go remote.Report(addrs[0], 0, codec, writerAttempt)
		outs, oks := client.CallAll(addrs[1:], ins, func(a string, in any) (any, bool) {
			return remote.Report(a, in, codec, apiserverAttempt)
		})
		for i := range outs {
			if !oks[i] {
				continue
			}
			answered++
			for _, l := range outs[i].([]comp.Log) {
				comp.CheckLog(l)
				logs++
			}
		}
	}
	if answered == 0 {
		return ended("no API server answered")
	}
	return Result{Checked: true, Why: itoa(logs) + " of " + itoa(rounds*(comp.Servers+comp.SharedServers)) +
		" API servers' logs, " + itoa(rounds) + " rounds"}
}
