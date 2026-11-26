// Package kvremote is the etcd-dist kv workload on Remote (notes/etcd-dist-plan.md, §2 and D8;
// examples/lib/remote, whose counter instance it follows): an orchestrator machine and one machine
// per client.
//
//   - The orchestrator (Orch) is remote.Run of txnlin's model, generator and history check: client
//     c's operations are calls to client machine c (remote.Do: a write gets one attempt and is an
//     unknown outcome, Output{Err: true}, if it gets no answer; a read up to remote.ReadTries).
//   - Client machine c (Node) is remote.ServeClient whose operation is txnlin.Call through its own
//     clientv3 client of the cluster (txnlin's call without prophecies: the orchestrator's Do makes
//     the prophecy).
//
// An operation whose call fails at the client machine (an etcd error) answers Output{Err: true}
// too: the far side's unknown outcome. txnlin's model takes it as a pending write (it may take
// effect later, at most once, or never) and a failed read as nothing.
package kvremote

import (
	"time"

	"github.com/anishathalye/porcupine"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/enc"
	"github.com/mit-pdos/etcd-grove/examples/etcd/txnlin"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// Attempt bounds one attempt of a call from the orchestrator to a client machine: longer than a
// client machine's operation (txnlin's calls give up after etcdstart.RequestTimeout), so that an
// attempt fails only on the network's faults.
const Attempt = etcdstart.RequestTimeout + 5*time.Second

func encCmp(e *enc.Enc, c txnlin.Cmp) {
	e.Int(c.Kind)
	e.Str(c.Key)
	e.Str(c.Val)
	e.I64(c.Num)
}

func decCmp(d *enc.Dec) txnlin.Cmp {
	var c txnlin.Cmp
	c.Kind = d.Int()
	c.Key = d.Str()
	c.Val = d.Str()
	c.Num = d.I64()
	return c
}

func encTOp(e *enc.Enc, o txnlin.TOp) {
	e.Int(o.Kind)
	e.Str(o.Key)
	e.Str(o.Val)
}

func decTOp(d *enc.Dec) txnlin.TOp {
	var o txnlin.TOp
	o.Kind = d.Int()
	o.Key = d.Str()
	o.Val = d.Str()
	return o
}

func encVR(e *enc.Enc, r txnlin.VR) {
	e.Str(r.Val)
	e.I64(r.Mod)
	e.I64(r.Ver)
}

func decVR(d *enc.Dec) txnlin.VR {
	var r txnlin.VR
	r.Val = d.Str()
	r.Mod = d.I64()
	r.Ver = d.I64()
	return r
}

func encTRes(e *enc.Enc, r txnlin.TRes) {
	e.Int(r.Kind)
	e.Bool(r.Found)
	encVR(e, r.R)
	e.I64(r.N)
}

func decTRes(d *enc.Dec) txnlin.TRes {
	var r txnlin.TRes
	r.Kind = d.Int()
	r.Found = d.Bool()
	r.R = decVR(d)
	r.N = d.I64()
	return r
}

func encKV(e *enc.Enc, kv txnlin.KV) {
	e.Str(kv.Key)
	encVR(e, kv.R)
}

func decKV(d *enc.Dec) txnlin.KV {
	var kv txnlin.KV
	kv.Key = d.Str()
	kv.R = decVR(d)
	return kv
}

// EncInput is in's encoding: every field, in order.
func EncInput(in txnlin.Input) []byte {
	e := &enc.Enc{}
	e.Int(in.Kind)
	e.Str(in.Key)
	e.Str(in.Val)
	e.Int(in.NCmps)
	encCmp(e, in.Cmp0)
	e.Int(in.NThen)
	encTOp(e, in.Then0)
	encTOp(e, in.Then1)
	encTOp(e, in.Then2)
	e.Int(in.NElse)
	encTOp(e, in.Else0)
	return e.B
}

// DecInput decodes EncInput's encoding.
func DecInput(b []byte) (txnlin.Input, bool) {
	d := enc.NewDec(b)
	var in txnlin.Input
	in.Kind = d.Int()
	in.Key = d.Str()
	in.Val = d.Str()
	in.NCmps = d.Int()
	in.Cmp0 = decCmp(d)
	in.NThen = d.Int()
	in.Then0 = decTOp(d)
	in.Then1 = decTOp(d)
	in.Then2 = decTOp(d)
	in.NElse = d.Int()
	in.Else0 = decTOp(d)
	return in, d.Done()
}

// EncOutput is o's encoding: every field, in order.
func EncOutput(o txnlin.Output) []byte {
	e := &enc.Enc{}
	e.Bool(o.Err)
	e.I64(o.Rev)
	e.Bool(o.Found)
	encVR(e, o.R)
	e.I64(o.N)
	e.Bool(o.Ok)
	e.Int(o.NRes)
	encTRes(e, o.Res0)
	encTRes(e, o.Res1)
	encTRes(e, o.Res2)
	e.Int(o.NKVs)
	encKV(e, o.KV0)
	encKV(e, o.KV1)
	encKV(e, o.KV2)
	return e.B
}

// DecOutput decodes EncOutput's encoding.
func DecOutput(b []byte) (txnlin.Output, bool) {
	d := enc.NewDec(b)
	var o txnlin.Output
	o.Err = d.Bool()
	o.Rev = d.I64()
	o.Found = d.Bool()
	o.R = decVR(d)
	o.N = d.I64()
	o.Ok = d.Bool()
	o.NRes = d.Int()
	o.Res0 = decTRes(d)
	o.Res1 = decTRes(d)
	o.Res2 = decTRes(d)
	o.NKVs = d.Int()
	o.KV0 = decKV(d)
	o.KV1 = decKV(d)
	o.KV2 = decKV(d)
	return o, d.Done()
}

// Codec is txnlin's codec: inputs and outputs as above; a read is an input txnlin's model does not
// take as a write (txnlin.IsWrite); the unknown output is Output{Err: true}.
func Codec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte { return EncInput(in.(txnlin.Input)) },
		DecIn: func(b []byte) (any, bool) {
			in, ok := DecInput(b)
			return in, ok
		},
		EncOut: func(out any) []byte { return EncOutput(out.(txnlin.Output)) },
		DecOut: func(b []byte) (any, bool) {
			o, ok := DecOutput(b)
			return o, ok
		},
		IsRead:    func(in any) bool { return !txnlin.IsWrite(in.(txnlin.Input)) },
		Unknown:   func(in any) any { return txnlin.Output{Err: true} },
		IsUnknown: func(out any) bool { return out.(txnlin.Output).Err },
	}
}

// Orch is the orchestrator: len(nodes) clients of ops operations each, client c's made at the
// client machine at nodes[c], the history checked by porcupine against txnlin's model within
// timeout (none if timeout <= 0). Its verdict (the theorem: never Illegal).
func Orch(nodes []string, ops int, timeout time.Duration) porcupine.CheckResult {
	return remote.Run(txnlin.Model(), nodes, Codec(), txnlin.Gen, ops, Attempt, timeout)
}

// Node is client machine c's program, at addr: a clientv3 client of the endpoints eps (in the
// order the client prefers), each operation it is asked txnlin.Call through it. It never returns,
// except at once if its client fails to be made (no retry: the orchestrator's calls to it then go
// unanswered).
func Node(c int, addr string, eps []string) {
	cli, err := etcdstart.NewClients(eps, zap.NewNop())
	if err != nil {
		return
	}
	newClient := func(int) any { return cli }
	op := func(sys any, in any) any {
		return txnlin.Call(sys.(*clientv3.Client), in)
	}
	remote.ServeClient(c, addr, newClient, op, Codec(), Attempt)
}
