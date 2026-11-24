// Package counter is remote's instance (notes/remote-port-plan.md, R4): a counter on a server
// machine of its own, behind two client machines, checked by an orchestrator machine. Four
// processes, each a command of cmd/:
//
//   - the orchestrator (Orch): remote.Check of two clients' increments and reads, each made at
//     the client's own machine, against the counter's model with pending increments (Model);
//   - client machine c (Client): remote.ServeClient whose operation is a remote.Do to the server;
//   - the server (Server): remote.Serve of lintest/counter's Counter (a mutex-protected counter,
//     proved logically atomic).
//
// Every call between two machines may fail: an increment whose call fails has an unknown outcome
// (Out{Unknown: true}), which may have taken effect, may take effect later, or never; a read
// whose calls fail answers unknown too, and constrains nothing.
package counter

import (
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	lcounter "github.com/mit-pdos/etcd-grove/examples/lib/lintest/counter"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// The deployment's addresses (each a machine's: a valid address of the net extension).
const (
	ServerAddr  = "127.0.0.1:7301"
	ClientAddr0 = "127.0.0.1:7302"
	ClientAddr1 = "127.0.0.1:7303"
)

// Ops is how many operations each client makes.
const Ops = 20

// AttemptMs bounds one attempt of a call between two machines.
const AttemptMs = 200

// Out is an operation's output: the counter's value it answered, or Unknown (the operation's
// outcome is unknown).
type Out struct {
	Unknown bool
	N       int64
}

// State is the model's state: the counter's least possible value Lo and the number K of
// increments that are pending (their calls failed: each may still take effect, once, or never).
// It stands for the configurations (Lo + j, K - j), 0 <= j <= K: the counter's value with the
// pending increments that have not yet taken effect.
type State struct {
	Lo int64
	K  int64
}

// step is the model's step on the configurations State stands for: an answered increment of N
// is one from a configuration after some pending ones took effect, an answered read of N one at
// such a configuration (the pending ones that took effect leave the pending count); an increment
// of unknown outcome is pending; a read of unknown outcome changes nothing.
func step(s State, incr bool, o Out) (bool, State) {
	if o.Unknown {
		if incr {
			return true, State{Lo: s.Lo, K: s.K + 1}
		}
		return true, s
	}
	if incr {
		if o.N < s.Lo+1 || o.N > s.Lo+s.K+1 {
			return false, s
		}
		return true, State{Lo: o.N, K: s.K - (o.N - 1 - s.Lo)}
	}
	if o.N < s.Lo || o.N > s.Lo+s.K {
		return false, s
	}
	return true, State{Lo: o.N, K: s.K - (o.N - s.Lo)}
}

// Model is the counter with pending increments (linkv's pending-writes model of the counter:
// increments are its writes), as a porcupine model. Inputs are bools (true: increment), outputs
// Outs.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return State{} },
		Step: func(state, input, output any) (bool, any) {
			ok, s := step(state.(State), input.(bool), output.(Out))
			return ok, s
		},
		Equal: func(a, b any) bool { return a.(State) == b.(State) },
	}
}

// Codec is the counter's codec: an input as one byte (1: increment), an output as one byte (1:
// unknown) and the value's 8 bytes, little-endian.
func Codec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte {
			if in.(bool) {
				return []byte{1}
			}
			return []byte{0}
		},
		DecIn: func(b []byte) (any, bool) {
			if len(b) != 1 || b[0] > 1 {
				return nil, false
			}
			return b[0] == 1, true
		},
		EncOut: func(out any) []byte {
			o := out.(Out)
			b := make([]byte, 9)
			if o.Unknown {
				b[0] = 1
			}
			n := uint64(o.N)
			for i := uint64(0); i < 8; i++ {
				b[1+i] = byte(n >> (8 * i))
			}
			return b
		},
		DecOut: func(b []byte) (any, bool) {
			if len(b) != 9 || b[0] > 1 {
				return nil, false
			}
			n := uint64(0)
			for i := uint64(0); i < 8; i++ {
				n = n | (uint64(b[1+i]) << (8 * i))
			}
			return Out{Unknown: b[0] == 1, N: int64(n)}, true
		},
		IsRead:    func(in any) bool { return !in.(bool) },
		Unknown:   func(in any) any { return Out{Unknown: true} },
		IsUnknown: func(out any) bool { return out.(Out).Unknown },
	}
}

// Gen is a client's next input: an increment or a read, at random.
func Gen(id int) any {
	return primitive.RandomUint64()%2 == 0
}

// attempt is AttemptMs as a duration.
func attempt() time.Duration {
	return time.Duration(AttemptMs) * time.Millisecond
}

// Orch is the orchestrator's program for the client machines at clientAddrs: it panics unless
// porcupine accepts the history of their operations.
func Orch(clientAddrs []string) {
	remote.Check(Model(), clientAddrs, Codec(), Gen, Ops, attempt())
}

// Client is client machine c's program, at addr, its operations made at the server at
// serverAddr.
func Client(c int, addr string, serverAddr string) {
	newClient := func(c int) any { return nil }
	op := func(_ any, in any) any {
		return remote.Do(serverAddr, in, Codec(), attempt())
	}
	remote.ServeClient(c, addr, newClient, op, Codec(), attempt())
}

// Server is the server's program, at addr: lintest/counter's Counter, served.
func Server(addr string) {
	op := func(sys any, in any) any {
		return Out{N: sys.(*lcounter.Counter).Apply(in).(int64)}
	}
	remote.Serve(addr, lcounter.New(), op, Codec(), attempt())
}
