// Package linkvtxn is the lintest driver instantiated with etcd over the KV API etcd's robustness
// tester drives (notes/linkv-txn-plan.md, stage D): one etcd member started in-process (as
// examples/putget does), a client connected to it, and lintest.Run with concurrent clients doing
// gets, lists, puts, deletes, multi-operation transactions and compare-and-sets of a few keys,
// checked by porcupine against a model of etcd's KV (Model, the Go form of the Lean model
// Proof/github_com/mit_pdos/etcd_grove/examples/linkvtxn/TxnModel.lean: robustness's EtcdState, a
// key's value, mod revision and version, the store's revision). Main panics if porcupine finds
// the history not linearizable; the theorem to prove is that it does not.
//
// Apply resolves a prophecy with whether the call returned no error (as the retired examples/linkv did), and,
// for a read (a get, a list, a transaction with no write), another with the revision the reply
// was read at. A prophecy has no effect when the program runs.
package linkvtxn

import (
	"context"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"go.uber.org/zap"

	"go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/common"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

// The kinds of operation (Input.Kind).
const (
	KGet  = 0
	KList = 1
	KPut  = 2
	KDel  = 3
	KTxn  = 4
)

// The kinds of a transaction's comparison (Cmp.Kind): a key's value, version or mod revision,
// for equality.
const (
	CValue   = 0
	CVersion = 1
	CMod     = 2
)

// The kinds of a transaction's operation (TOp.Kind).
const (
	TGet = 0
	TPut = 1
	TDel = 2
)

// A Cmp is a comparison of a transaction: the key's value is Val (CValue), or its version or mod
// revision is Num (0 for a missing key).
type Cmp struct {
	Kind int
	Key  string
	Val  string
	Num  int64
}

// A TOp is an operation of a transaction: a get, a put of Val, or a delete, of Key.
type TOp struct {
	Kind int
	Key  string
	Val  string
}

// An Input is an operation: a get of Key, a list of the keys, a put of Key with Val, a delete of
// Key, or a transaction (If(Cmps).Then(Then).Else(Else): its comparisons, then- and
// else-operations the first NCmps, NThen and NElse of Cmp0, Then0..Then2 and Else0). An Input is
// a plain value (no slice: porcupine's model decodes it purely, Proof/.../linkvtxn).
type Input struct {
	Kind  int
	Key   string
	Val   string
	NCmps int
	Cmp0  Cmp
	NThen int
	Then0 TOp
	Then1 TOp
	Then2 TOp
	NElse int
	Else0 TOp
}

// The most comparisons, then- and else-operations a transaction has (Input's fields).
const (
	MaxCmps = 1
	MaxThen = 3
	MaxElse = 1
)

// cmpsOf is a transaction's comparisons (a new slice).
func cmpsOf(in Input) []Cmp {
	out := []Cmp{}
	if in.NCmps > 0 {
		out = append(out, in.Cmp0)
	}
	return out
}

// thenOf is a transaction's then-operations (a new slice).
func thenOf(in Input) []TOp {
	out := []TOp{}
	if in.NThen > 0 {
		out = append(out, in.Then0)
	}
	if in.NThen > 1 {
		out = append(out, in.Then1)
	}
	if in.NThen > 2 {
		out = append(out, in.Then2)
	}
	return out
}

// elseOf is a transaction's else-operations (a new slice).
func elseOf(in Input) []TOp {
	out := []TOp{}
	if in.NElse > 0 {
		out = append(out, in.Else0)
	}
	return out
}

// A VR is a key's value, mod revision and version.
type VR struct {
	Val string
	Mod int64
	Ver int64
}

// A KV is a key with its value.
type KV struct {
	Key string
	R   VR
}

// A TRes is a transaction operation's result: a get's (Found, R), a put's, a delete's count N.
type TRes struct {
	Kind  int
	Found bool
	R     VR
	N     int64
}

// An Output is an operation's result: Err if the call returned an error; otherwise the reply's
// revision and, by the input's kind, a get's (Found, R), a list's key-values (the first NKVs of
// KV0..KV2), a delete's count N, a transaction's verdict Ok and its operations' results (the first
// NRes of Res0..Res2). More results than the fields hold leave the count above them, which the
// model rejects. A plain value, as Input.
type Output struct {
	Err   bool
	Rev   int64
	Found bool
	R     VR
	N     int64
	Ok    bool
	NRes  int
	Res0  TRes
	Res1  TRes
	Res2  TRes
	NKVs  int
	KV0   KV
	KV1   KV
	KV2   KV
}

// resOf is a transaction output's results (a new slice; at most 3).
func resOf(o Output) []TRes {
	out := []TRes{}
	if o.NRes > 0 {
		out = append(out, o.Res0)
	}
	if o.NRes > 1 {
		out = append(out, o.Res1)
	}
	if o.NRes > 2 {
		out = append(out, o.Res2)
	}
	return out
}

// kvsOf is a list output's key-values (a new slice; at most 3).
func kvsOf(o Output) []KV {
	out := []KV{}
	if o.NKVs > 0 {
		out = append(out, o.KV0)
	}
	if o.NKVs > 1 {
		out = append(out, o.KV1)
	}
	if o.NKVs > 2 {
		out = append(out, o.KV2)
	}
	return out
}

// withRes is o with the results rs (their count; the first 3).
func withRes(o Output, rs []TRes) Output {
	o.NRes = len(rs)
	if len(rs) > 0 {
		o.Res0 = rs[0]
	}
	if len(rs) > 1 {
		o.Res1 = rs[1]
	}
	if len(rs) > 2 {
		o.Res2 = rs[2]
	}
	return o
}

// withKVs is o with the key-values kvs (their count; the first 3).
func withKVs(o Output, kvs []KV) Output {
	o.NKVs = len(kvs)
	if len(kvs) > 0 {
		o.KV0 = kvs[0]
	}
	if len(kvs) > 1 {
		o.KV1 = kvs[1]
	}
	if len(kvs) > 2 {
		o.KV2 = kvs[2]
	}
	return o
}

// The workload's keys, in order, and what List lists: the range [listFrom, listTo), which holds
// them.
const listFrom = "k"
const listTo = "l"

// workloadKeys are the keys Gen picks from (sorted), as a function so that the package's
// initializer runs no code.
func workloadKeys() []string {
	return []string{"k0", "k1", "k2"}
}

// ---------------------------------------------------------------------------------------------
// The model (TxnModel.lean's mStep, over configurations with pending failed writes)

// An entry of the store: a key and its value.
type entry struct {
	key string
	r   VR
}

// A store at a revision: its entries sorted by key, and the revision.
type store struct {
	kvs []entry
	rev int64
}

// A configuration: a store and the failed writes that may still take effect.
type mcfg struct {
	st   store
	pend []Input
}

// A state is the set of configurations the history may have reached (no duplicates).
type state []mcfg

func lookup(kvs []entry, k string) (VR, bool) {
	for _, e := range kvs {
		if e.key == k {
			return e.r, true
		}
	}
	return VR{}, false
}

// setKey returns kvs with k's value r (a new slice, sorted).
func setKey(kvs []entry, k string, r VR) []entry {
	out := make([]entry, 0, len(kvs)+1)
	done := false
	for _, e := range kvs {
		if !done && k <= e.key {
			out = append(out, entry{key: k, r: r})
			done = true
			if e.key == k {
				continue
			}
		}
		out = append(out, e)
	}
	if !done {
		out = append(out, entry{key: k, r: r})
	}
	return out
}

// delKey returns kvs without k (a new slice).
func delKey(kvs []entry, k string) []entry {
	out := make([]entry, 0, len(kvs))
	for _, e := range kvs {
		if e.key != k {
			out = append(out, e)
		}
	}
	return out
}

// put returns kvs after a put of k with v at revision r: the key's version one more.
func put(kvs []entry, r int64, k string, v string) []entry {
	old, ok := lookup(kvs, k)
	ver := int64(1)
	if ok {
		ver = old.Ver + 1
	}
	return setKey(kvs, k, VR{Val: v, Mod: r, Ver: ver})
}

// holds is a comparison's verdict on the store (TxnModel.lean's MCmp.holds).
func holds(kvs []entry, c Cmp) bool {
	r, ok := lookup(kvs, c.Key)
	if c.Kind == CValue {
		return ok && r.Val == c.Val
	}
	if c.Kind == CVersion {
		return r.Ver == c.Num
	}
	return r.Mod == c.Num
}

// runOps runs a transaction's operations at revision r (TxnModel.lean's runOps): the store
// after them, their results, and whether they changed the store.
func runOps(kvs []entry, r int64, ops []TOp) ([]entry, []TRes, bool) {
	res := make([]TRes, 0, len(ops))
	changed := false
	for _, op := range ops {
		if op.Kind == TGet {
			v, ok := lookup(kvs, op.Key)
			res = append(res, TRes{Kind: TGet, Found: ok, R: v})
		} else if op.Kind == TPut {
			kvs = put(kvs, r, op.Key, op.Val)
			res = append(res, TRes{Kind: TPut})
			changed = true
		} else {
			_, ok := lookup(kvs, op.Key)
			if ok {
				kvs = delKey(kvs, op.Key)
				res = append(res, TRes{Kind: TDel, N: 1})
				changed = true
			} else {
				res = append(res, TRes{Kind: TDel, N: 0})
			}
		}
	}
	return kvs, res, changed
}

// mstep is an operation's effect on the store and its output (TxnModel.lean's mStep).
func mstep(in Input, st store) (store, Output) {
	if in.Kind == KGet {
		v, ok := lookup(st.kvs, in.Key)
		return st, Output{Rev: st.rev, Found: ok, R: v}
	}
	if in.Kind == KList {
		kvs := make([]KV, 0, len(st.kvs))
		for _, e := range st.kvs {
			kvs = append(kvs, KV{Key: e.key, R: e.r})
		}
		return st, withKVs(Output{Rev: st.rev}, kvs)
	}
	if in.Kind == KPut {
		r := st.rev + 1
		return store{kvs: put(st.kvs, r, in.Key, in.Val), rev: r}, Output{Rev: r}
	}
	if in.Kind == KDel {
		_, ok := lookup(st.kvs, in.Key)
		if ok {
			r := st.rev + 1
			return store{kvs: delKey(st.kvs, in.Key), rev: r}, Output{Rev: r, N: 1}
		}
		return st, Output{Rev: st.rev, N: 0}
	}
	ok := true
	for _, c := range cmpsOf(in) {
		if !holds(st.kvs, c) {
			ok = false
		}
	}
	ops := elseOf(in)
	if ok {
		ops = thenOf(in)
	}
	kvs, res, changed := runOps(st.kvs, st.rev+1, ops)
	rev := st.rev
	if changed {
		rev = st.rev + 1
	}
	return store{kvs: kvs, rev: rev}, withRes(Output{Rev: rev, Ok: ok}, res)
}

// isWrite reports whether an operation may write (a failed one may take effect later).
func isWrite(in Input) bool {
	if in.Kind == KPut || in.Kind == KDel {
		return true
	}
	if in.Kind != KTxn {
		return false
	}
	for _, op := range thenOf(in) {
		if op.Kind != TGet {
			return true
		}
	}
	for _, op := range elseOf(in) {
		if op.Kind != TGet {
			return true
		}
	}
	return false
}

func vrEqual(a, b VR) bool {
	return a.Val == b.Val && a.Mod == b.Mod && a.Ver == b.Ver
}

// outEqual compares an output with the model's for an input of kind kind (only the fields that
// kind answers).
func outEqual(kind int, a, b Output) bool {
	if a.Err || b.Err || a.Rev != b.Rev {
		return false
	}
	if kind == KGet {
		return a.Found == b.Found && (!a.Found || vrEqual(a.R, b.R))
	}
	if kind == KList {
		if a.NKVs != b.NKVs || a.NKVs > 3 {
			return false
		}
		ak := kvsOf(a)
		bk := kvsOf(b)
		for i := range ak {
			if ak[i].Key != bk[i].Key || !vrEqual(ak[i].R, bk[i].R) {
				return false
			}
		}
		return true
	}
	if kind == KPut {
		return true
	}
	if kind == KDel {
		return a.N == b.N
	}
	if a.Ok != b.Ok || a.NRes != b.NRes || a.NRes > 3 {
		return false
	}
	ar := resOf(a)
	br := resOf(b)
	for i := range ar {
		if !resEqual(ar[i], br[i]) {
			return false
		}
	}
	return true
}

// resEqual compares a transaction operation's result with the model's (only the fields its kind
// answers: a get's (Found, R), a delete's N).
func resEqual(x, y TRes) bool {
	if x.Kind != y.Kind {
		return false
	}
	if x.Kind == TGet {
		return x.Found == y.Found && (!x.Found || vrEqual(x.R, y.R))
	}
	if x.Kind == TDel {
		return x.N == y.N
	}
	return true
}

func inputEqual(a, b Input) bool {
	return a == b
}

func storeEqual(a, b store) bool {
	if a.rev != b.rev || len(a.kvs) != len(b.kvs) {
		return false
	}
	for i := range a.kvs {
		if a.kvs[i].key != b.kvs[i].key || !vrEqual(a.kvs[i].r, b.kvs[i].r) {
			return false
		}
	}
	return true
}

func configEqual(a, b mcfg) bool {
	if !storeEqual(a.st, b.st) || len(a.pend) != len(b.pend) {
		return false
	}
	for i := range a.pend {
		if !inputEqual(a.pend[i], b.pend[i]) {
			return false
		}
	}
	return true
}

func addConfig(s state, c mcfg) state {
	for _, d := range s {
		if configEqual(c, d) {
			return s
		}
	}
	return append(s, c)
}

// removeAt returns pend without its i-th input (a new slice).
func removeAt(pend []Input, i int) []Input {
	out := make([]Input, 0, len(pend))
	out = append(out, pend[:i]...)
	return append(out, pend[i+1:]...)
}

// closure adds to s every configuration reachable by pending writes taking effect.
func closure(s state) state {
	out := state{}
	work := append([]mcfg{}, s...)
	for len(work) > 0 {
		c := work[len(work)-1]
		work = work[:len(work)-1]
		n := len(out)
		out = addConfig(out, c)
		if len(out) == n {
			continue
		}
		for i, w := range c.pend {
			st, _ := mstep(w, c.st)
			work = append(work, mcfg{st: st, pend: removeAt(c.pend, i)})
		}
	}
	return out
}

// step returns the configurations c steps to by (in, out): a call that returned no error took
// effect and answered the model's output; a failed write becomes pending; a failed read does
// nothing.
func step(c mcfg, in Input, out Output) []mcfg {
	if out.Err {
		if isWrite(in) {
			pend := make([]Input, 0, len(c.pend)+1)
			pend = append(pend, in)
			pend = append(pend, c.pend...)
			return []mcfg{{st: c.st, pend: pend}}
		}
		return []mcfg{c}
	}
	st, o := mstep(in, c.st)
	if !outEqual(in.Kind, out, o) {
		return nil
	}
	return []mcfg{{st: st, pend: c.pend}}
}

// Model is etcd's KV as a porcupine model: the store starts empty at revision 1; a call that
// returned no error took effect at once and answered as the model; a failed write may take
// effect at any later time, or never; a failed read constrains nothing.
func Model() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return state{mcfg{st: store{rev: 1}}} },
		Step: func(st, input, output any) (bool, any) {
			in := input.(Input)
			out := output.(Output)
			next := state{}
			for _, c := range st.(state) {
				for _, d := range step(c, in, out) {
					next = addConfig(next, d)
				}
			}
			next = closure(next)
			return len(next) > 0, next
		},
		Equal: func(a, b any) bool {
			sa := a.(state)
			sb := b.(state)
			if len(sa) != len(sb) {
				return false
			}
			for i := range sa {
				if !configEqual(sa[i], sb[i]) {
					return false
				}
			}
			return true
		},
	}
}

// ---------------------------------------------------------------------------------------------
// The workload (robustness's EtcdPutDeleteLease traffic, without leases and stale reads)

// pick returns n mod m and n / m.
func pick(n uint64, m uint64) (uint64, uint64) {
	return n % m, n / m
}

// genFrom is the operation Gen picks for the random number n, with robustness's weights (out of
// 63): a get (15), a list (8), a put (20), a delete (5), a transaction of up to three operations
// on distinct keys (10), or a compare-and-set (5): if the key's value, version or mod revision is
// as guessed, put a new value, else get it.
func genFrom(n uint64) Input {
	keys := workloadKeys()
	vals := []string{"a", "b", "c", "d"}
	w, n := pick(n, 63)
	ki, n := pick(n, uint64(len(keys)))
	vi, n := pick(n, uint64(len(vals)))
	k := keys[ki]
	v := vals[vi]
	if w < 15 {
		return Input{Kind: KGet, Key: k}
	}
	if w < 23 {
		return Input{Kind: KList}
	}
	if w < 43 {
		return Input{Kind: KPut, Key: k, Val: v}
	}
	if w < 48 {
		return Input{Kind: KDel, Key: k}
	}
	if w < 58 {
		// one to three operations, on the keys from ki on (distinct)
		cnt, n := pick(n, 3)
		k0, n := pick(n, 3)
		k1, n := pick(n, 3)
		k2, _ := pick(n, 3)
		return Input{Kind: KTxn, NThen: int(cnt) + 1,
			Then0: TOp{Kind: int(k0), Key: keys[ki], Val: v},
			Then1: TOp{Kind: int(k1), Key: keys[(ki+1)%uint64(len(keys))], Val: v},
			Then2: TOp{Kind: int(k2), Key: keys[(ki+2)%uint64(len(keys))], Val: v}}
	}
	ck, n := pick(n, 3)
	guess, _ := pick(n, 4)
	nv := vals[(vi+1)%uint64(len(vals))]
	return Input{Kind: KTxn, NCmps: 1, Cmp0: Cmp{Kind: int(ck), Key: k, Val: v, Num: int64(guess)},
		NThen: 1, Then0: TOp{Kind: TPut, Key: k, Val: nv}, NElse: 1, Else0: TOp{Kind: TGet, Key: k}}
}

// Gen picks an operation at random (genFrom of a random number).
func Gen(id int) any {
	return genFrom(primitive.RandomUint64())
}

// ---------------------------------------------------------------------------------------------
// The calls

func vrOf(value []byte, mod int64, ver int64) VR {
	return VR{Val: string(value), Mod: mod, Ver: ver}
}

func cmpOf(c Cmp) clientv3.Cmp {
	if c.Kind == CValue {
		return clientv3.Compare(clientv3.Value(c.Key), "=", c.Val)
	}
	if c.Kind == CVersion {
		return clientv3.Compare(clientv3.Version(c.Key), "=", c.Num)
	}
	return clientv3.Compare(clientv3.ModRevision(c.Key), "=", c.Num)
}

func opOf(op TOp) clientv3.Op {
	if op.Kind == TGet {
		return clientv3.OpGet(op.Key)
	}
	if op.Kind == TPut {
		return clientv3.OpPut(op.Key, op.Val)
	}
	return clientv3.OpDelete(op.Key)
}

func opsOf(ops []TOp) []clientv3.Op {
	out := make([]clientv3.Op, 0, len(ops))
	for _, op := range ops {
		out = append(out, opOf(op))
	}
	return out
}

// Every call below is made in a context with the examples' request timeout
// (common.RequestTimeout, cancelled after the call), as etcd's clients are used in practice: a
// call that takes longer fails (context.DeadlineExceeded) and the operation is recorded as failed.

// callGet runs a get of key through the client cli: its output.
func callGet(cli *clientv3.Client, key string) Output {
	ctx, cancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	resp, err := cli.Get(ctx, key)
	cancel()
	if err != nil {
		return Output{Err: true}
	}
	out := Output{Rev: resp.Header.Revision}
	if len(resp.Kvs) > 0 {
		kv := resp.Kvs[0]
		out.Found = true
		out.R = vrOf(kv.Value, kv.ModRevision, kv.Version)
	}
	return out
}

// kvsFrom is the KVs of a reply's key-values.
func kvsFrom(kvs []*mvccpb.KeyValue) []KV {
	out := make([]KV, 0, len(kvs))
	for _, kv := range kvs {
		out = append(out, KV{Key: string(kv.Key), R: vrOf(kv.Value, kv.ModRevision, kv.Version)})
	}
	return out
}

// callList runs a list of the keys through the client cli: its output.
func callList(cli *clientv3.Client) Output {
	ctx, cancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	resp, err := cli.Get(ctx, listFrom, clientv3.WithRange(listTo))
	cancel()
	if err != nil {
		return Output{Err: true}
	}
	return withKVs(Output{Rev: resp.Header.Revision}, kvsFrom(resp.Kvs))
}

// callPut runs a put of key with val through the client cli: its output.
func callPut(cli *clientv3.Client, key string, val string) Output {
	ctx, cancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	resp, err := cli.Put(ctx, key, val)
	cancel()
	if err != nil {
		return Output{Err: true}
	}
	return Output{Rev: resp.Header.Revision}
}

// callDel runs a delete of key through the client cli: its output.
func callDel(cli *clientv3.Client, key string) Output {
	ctx, cancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	resp, err := cli.Delete(ctx, key)
	cancel()
	if err != nil {
		return Output{Err: true}
	}
	return Output{Rev: resp.Header.Revision, N: resp.Deleted}
}

// cmpsFor is the client's comparisons of a transaction (a new slice).
func cmpsFor(in Input) []clientv3.Cmp {
	cmps := make([]clientv3.Cmp, 0, in.NCmps)
	for _, c := range cmpsOf(in) {
		cmps = append(cmps, cmpOf(c))
	}
	return cmps
}

// txnRes is the results of a transaction's responses, for its branch's operations ops.
func txnRes(ops []TOp, resps []*etcdserverpb.ResponseOp) []TRes {
	res := make([]TRes, 0, len(resps))
	for i, r := range resps {
		kind := TGet
		if i < len(ops) {
			kind = ops[i].Kind
		}
		if kind == TGet {
			rr := r.GetResponseRange()
			t := TRes{Kind: TGet}
			if rr != nil && len(rr.Kvs) > 0 {
				kv := rr.Kvs[0]
				t.Found = true
				t.R = vrOf(kv.Value, kv.ModRevision, kv.Version)
			}
			res = append(res, t)
		} else if kind == TPut {
			res = append(res, TRes{Kind: TPut})
		} else {
			t := TRes{Kind: TDel}
			if dr := r.GetResponseDeleteRange(); dr != nil {
				t.N = dr.Deleted
			}
			res = append(res, t)
		}
	}
	return res
}

// callTxn runs a transaction through the client cli: its output.
func callTxn(cli *clientv3.Client, in Input) Output {
	ctx, cancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	resp, err := cli.Txn(ctx).If(cmpsFor(in)...).Then(opsOf(thenOf(in))...).Else(opsOf(elseOf(in))...).Commit()
	cancel()
	if err != nil {
		return Output{Err: true}
	}
	ops := elseOf(in)
	if resp.Succeeded {
		ops = thenOf(in)
	}
	return withRes(Output{Rev: resp.Header.Revision, Ok: resp.Succeeded}, txnRes(ops, resp.Responses))
}

// call runs one operation through the client cli: its output.
func call(cli *clientv3.Client, in Input) Output {
	if in.Kind == KGet {
		return callGet(cli, in.Key)
	}
	if in.Kind == KList {
		return callList(cli)
	}
	if in.Kind == KPut {
		return callPut(cli, in.Key, in.Val)
	}
	if in.Kind == KDel {
		return callDel(cli, in.Key)
	}
	return callTxn(cli, in)
}

// Apply runs one operation through the client cli, resolving a prophecy with its outcome and,
// for a read, another with the revision it read at (0 otherwise).
func Apply(cli *clientv3.Client, input any) any {
	in := input.(Input)
	p := primitive.NewProph()
	rp := primitive.NewProph()
	out := call(cli, in)
	var rev uint64
	if !out.Err && !isWrite(in) {
		rev = uint64(out.Rev)
	}
	p.ResolveBool(!out.Err)
	rp.ResolveU64(rev)
	return out
}

// Check runs lintest.Run of clients concurrent clients of cli, each running ops operations, and
// returns porcupine's verdict.
func Check(cli *clientv3.Client, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	apply := func(input any) any { return Apply(cli, input) }
	return lintest.Run(Model(), apply, Gen, lintest.CounterClock(), clients, ops, timeout)
}

// The client address: the string net.Listen is given is the client's endpoint, verbatim (a plain
// host:port, no scheme). Not the other examples', so that their tests can run at once.
const clientAddr = "127.0.0.1:23796"

// Main starts one member of a new cluster (as examples/linkv's Main does), connects a client
// with etcd's default configuration and runs Check; it panics if porcupine finds the history
// illegal. An error from a step before Check ends Main without a check.
func Main(clients int, ops int) porcupine.CheckResult {
	lg := zap.NewNop()
	s, err := common.StartServer("linkvtxn", "127.0.0.1:23806", clientAddr, lg)
	if err != nil {
		return porcupine.Unknown
	}
	if err := common.Serve(s, clientAddr); err != nil {
		return porcupine.Unknown
	}

	// etcd's default client configuration (its default retries): the server never answers with a
	// refusal (authentication off, a voter), so a write is sent at most once and the server applies
	// it at most once, while a read may be retried (decision D29).
	cli, err := common.NewClient(clientAddr, lg)
	if err != nil {
		return porcupine.Unknown
	}
	r := Check(cli, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("linkvtxn: porcupine found the history not linearizable")
	}
	return r
}
