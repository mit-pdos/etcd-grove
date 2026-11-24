package client

import (
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/etcd/auth"
	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/deployment"
	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/enc"
	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/kvremote"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// Clients on machines of their own (the plan's §2, D8; examples/lib/remote): a workload with
// several clients is an orchestrator machine (MainReady, given the client machines' addresses)
// and one client machine per client (NodeMain), which serves the orchestrator's calls with a
// clientv3 client of its own and never returns:
//
//   - kv: client machine c is kvremote.Node (each call one of txnlin's operations, txnlin.Call);
//     the orchestrator is kvremote.Orch (remote.Run: generation, call and return stamps, the
//     history, porcupine);
//   - watch, cache: client machine c is writer c (one call: its Puts, given by the orchestrator,
//     done with etcdstart.Writer; it answers its log of the Puts that returned); the orchestrator
//     calls every writer at once with reportAll and keeps the watch (or the cache) and the
//     check. A writer that does not answer (its call failed, or timed out) is taken to have tried
//     all of its Puts and had none succeed: every event of its Puts is then attempted, none is
//     required;
//   - auth: client machine c is principal auth.Principals()[c] (one call: auth.Work through a client
//     of its own, made for the call, which checks its own refusals and replies, a panic on that
//     machine if one fails); the orchestrator does the set-up, the barriers, root's last Put and
//     the history checks. A principal that does not answer changes nothing in the checks, which
//     read what was applied.
//
// The single-client workloads (compact, putget, durable, the lease workloads, authLease: their
// clients are sequential steps of one orchestration) have no client machine.

// How long a call from the orchestrator to a client machine may take: a writer's whole loop (each
// Put within the request timeout), a principal's whole auth.Work (a dozen requests and a refused
// watch's wait). A call that takes longer is a call without an answer (see above).
func writerAttempt(nops int) time.Duration {
	return time.Duration(nops)*etcdstart.RequestTimeout + 30*time.Second
}

const principalAttempt = 3 * time.Minute

// writerCodec is a writer's call: its Puts in, its log of those that returned out.
func writerCodec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte {
			ps := in.([]etcdstart.KV)
			e := &enc.Enc{}
			e.Int(len(ps))
			for _, p := range ps {
				e.Str(p.Key)
				e.Str(p.Val)
			}
			return e.B
		},
		DecIn: func(b []byte) (any, bool) {
			d := enc.NewDec(b)
			n := d.Int()
			var ps []etcdstart.KV
			for i := 0; d.Ok && i < n; i++ {
				ps = append(ps, etcdstart.KV{Key: d.Str(), Val: d.Str()})
			}
			return ps, d.Done()
		},
		EncOut: func(out any) []byte {
			rs := out.([]etcdstart.PutRec)
			e := &enc.Enc{}
			e.Int(len(rs))
			for _, r := range rs {
				e.I64(r.Rev)
				e.Str(r.Key)
				e.Str(r.Val)
			}
			return e.B
		},
		DecOut: func(b []byte) (any, bool) {
			d := enc.NewDec(b)
			n := d.Int()
			var rs []etcdstart.PutRec
			for i := 0; d.Ok && i < n; i++ {
				rs = append(rs, etcdstart.PutRec{Rev: d.I64(), Key: d.Str(), Val: d.Str()})
			}
			return rs, d.Done()
		},
	}
}

// writerOp is a writer machine's call: its Puts through its own client (etcdstart.Writer), and the
// log of those that returned.
func writerOp(sys any, in any) any {
	ps := in.([]etcdstart.KV)
	w := &etcdstart.Writes{}
	etcdstart.Writer(sys.(*clientv3.Client), w, ps, 0, len(ps))
	w.Mu.Lock()
	oks := w.Ok
	w.Mu.Unlock()
	if oks == nil {
		oks = []etcdstart.PutRec{}
	}
	return oks
}

// remoteWriters runs the writers at the client machines nodes, writer c's Puts tried[c*nops,
// (c+1)*nops), all at once, and returns the successful Puts their logs report (none of a writer
// that did not answer).
func remoteWriters(nodes []string, tried []etcdstart.KV, nops int) []etcdstart.PutRec {
	ins := make([]any, len(nodes))
	for c := range nodes {
		ins[c] = tried[c*nops : (c+1)*nops]
	}
	outs, oks := reportAll(nodes, ins, writerCodec(), writerAttempt(nops))
	var all []etcdstart.PutRec
	for c := range nodes {
		if oks[c] {
			all = append(all, outs[c].([]etcdstart.PutRec)...)
		}
	}
	return all
}

// principalCodec is a principal's call: its name in, whether auth.Work ran out (false: its client
// failed to connect).
func principalCodec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte {
			e := &enc.Enc{}
			e.Str(in.(string))
			return e.B
		},
		DecIn: func(b []byte) (any, bool) {
			d := enc.NewDec(b)
			s := d.Str()
			return s, d.Done()
		},
		EncOut: func(out any) []byte {
			e := &enc.Enc{}
			e.Bool(out.(bool))
			return e.B
		},
		DecOut: func(b []byte) (any, bool) {
			d := enc.NewDec(b)
			x := d.Bool()
			return x, d.Done()
		},
	}
}

// principalClient connects who's client (RunAuth's choices: u and the client with an invalid token
// through eps[1 mod k], v through eps[2 mod k] as their users, the client with no token through
// eps[0]).
func principalClient(eps []string, who string) (*clientv3.Client, error) {
	k := len(eps)
	switch who {
	case "u":
		return newUserClient(eps[1%k], "u", uPw)
	case "v":
		return newUserClient(eps[2%k], "v", vPw)
	case "bad":
		return newClient([]string{eps[1%k]})
	}
	return newClient([]string{eps[0]})
}

// principalOp is a principal machine's call for principal who: auth.Work through a client of its
// own (sys is the endpoints), made for the call and closed after it.
func principalOp(sys any, in any) any {
	who := in.(string)
	cli, err := principalClient(sys.([]string), who)
	if err != nil {
		return false
	}
	defer cli.Close()
	auth.Work(cli, who)
	return true
}

// remotePrincipals runs every principal's auth.Work at its client machine (nodes[c] is principal
// auth.Principals()[c]'s), all at once, and reports how many answered that it ran.
func remotePrincipals(nodes []string) int {
	ps := auth.Principals()
	ins := make([]any, len(ps))
	for c := range ps {
		ins[c] = ps[c]
	}
	outs, oks := reportAll(nodes, ins, principalCodec(), principalAttempt)
	n := 0
	for c := range ps {
		if oks[c] && outs[c].(bool) {
			n++
		}
	}
	return n
}

// ConnectRetry makes a client of eps, trying every 100ms until it succeeds (a client machine has
// nothing else to do).
func ConnectRetry(eps []string) *clientv3.Client {
	for {
		cli, err := newClient(eps)
		if err == nil {
			return cli
		}
		time.Sleep(100 * time.Millisecond)
	}
}

// NodeMain is client machine c of workload w (deployment.NodeCount(w) > c), listening at addr, the members'
// client endpoints eps: it serves the
// orchestrator's calls (see above). It never returns (for a workload without client machines, it
// returns at once).
func NodeMain(w deployment.Workload, c int, addr string, eps []string) {
	if c < 0 || c >= deployment.NodeCount(w) || len(eps) == 0 {
		return
	}
	switch w.Kind {
	case deployment.KV:
		kvremote.Node(c, addr, Rotate(eps, c))
	case deployment.Watch, deployment.Cache:
		newClient := func(c int) any { return ConnectRetry(Rotate(eps, c)) }
		remote.ServeClient(c, addr, newClient, writerOp, writerCodec(), writerAttempt(w.Ops))
	case deployment.Auth:
		newClient := func(int) any { return eps }
		remote.ServeClient(c, addr, newClient, principalOp, principalCodec(), principalAttempt)
	}
}

// reportAll runs remote.Report at every client machine nodes[c] with input ins[c], all at once
// (CallAll), and returns their outputs and whether each answered.
func reportAll(nodes []string, ins []any, codec remote.Codec, d time.Duration) ([]any, []bool) {
	return CallAll(nodes, ins, func(a string, in any) (any, bool) { return remote.Report(a, in, codec, d) })
}
