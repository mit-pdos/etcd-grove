// Package k8setcd3 is the lintest driver instantiated with Kubernetes' etcd3 storage backend
// (k8s.io/apiserver/pkg/storage/etcd3, over this repository's etcd fork; notes/k8s-etcd3-plan.md,
// phase 6): one etcd member started in-process (as examples/linkvtxn does), a kubernetes client
// connected to it, the etcd3 store over that client with the driver's own object type, codec,
// versioner, decoder and (identity) transformer, and lintest.Run with concurrent clients doing
// the store's unary operations (Create, Delete, GuaranteedUpdate, Get) on a few keys, checked by
// porcupine against Model.
//
// Model is a Go copy of Kubernetes' storage test model, correctness.Model
// (k8s.io/apiserver/pkg/storage/testing/correctness/model.go), specialized to the driver's
// object type, as close to the original as possible (D30m): the same operations, the same
// answers and errors (the storage errors' code, key and resource version; the callbacks' own
// errors), the same no-op rule for an update, and the same re-run of the operation's callbacks
// (tryUpdate, validateDeletion) on the model's object. The one change is D30g's: the model knows
// whether a stored value is the store's current encoding of its object (an item's canonical
// bit), and an update is a no-op only on a canonical item, as the store's is
// (issues/k8s-correctness-model-noop-rewrite.md). The driver seeds some keys with values in an
// older encoding (the codec still decodes them), so the traffic reaches that case.
//
// As examples/linkvtxn's model, Model runs over configurations with pending failed writes: a
// call that returned no error took effect at once and answered as the model; a failed write may
// take effect at any later time, or never; a failed read constrains nothing.
//
// The traffic is the minimal unary traffic of Kubernetes' storage correctness test
// (test/integration/apiserver/storage/traffic.go): consistent Gets (no resource version), Creates
// without a resource version or TTL, Deletes and GuaranteedUpdates without preconditions or a
// cached object, updates without ignoreNotFound or a TTL, with the test's rejecting
// validateDeletion and tryUpdate (a sentinel error when the stored object's value is the one
// drawn) and its no-op updates. Main panics if porcupine finds the history not linearizable; the
// theorem to prove is that it does not.
package k8setcd3

import (
	"context"
	"errors"
	"io"
	"net"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"

	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage"
	"k8s.io/apiserver/pkg/storage/etcd3"
	"k8s.io/apiserver/pkg/storage/value"

	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

// ---------------------------------------------------------------------------------------------
// The driver's objects, codec, versioner, decoder and transformer

// An Obj is the driver's object: its name (the key it is stored at), a value, and its resource
// version (0 for none). Kubernetes' objects keep it as a decimal string; the driver keeps the
// number, and its versioner's string form of it is rvString's.
type Obj struct {
	Name            string
	Value           string
	ResourceVersion uint64
}

// GetObjectKind is runtime.Object's: the driver's objects carry no kind.
func (o *Obj) GetObjectKind() schema.ObjectKind {
	return schema.EmptyObjectKind
}

// DeepCopyObject is runtime.Object's: a copy.
func (o *Obj) DeepCopyObject() runtime.Object {
	c := *o
	return &c
}

// The current encoding's tag, and the older one the codec still decodes.
const (
	tagV1 = "v1:"
	tagV0 = "v0:"
)

// encodeWith is the encoding of an object's name and value (not its resource version) under the
// tag tag: the tag, the name's length (one byte; names are shorter than 256 bytes), the name and
// the value.
func encodeWith(tag string, name string, val string) []byte {
	out := []byte(tag)
	out = append(out, byte(len(name)))
	out = append(out, []byte(name)...)
	return append(out, []byte(val)...)
}

// encodeObj is the current encoding of an object.
func encodeObj(o *Obj) []byte {
	return encodeWith(tagV1, o.Name, o.Value)
}

// encodeV0 is the older encoding. The driver seeds some keys with it.
func encodeV0(name string, val string) []byte {
	return encodeWith(tagV0, name, val)
}

// decodeObj decodes either encoding: the name and value, or false.
func decodeObj(data []byte) (string, string, bool) {
	if len(data) < 4 {
		return "", "", false
	}
	tag := string(data[:3])
	if tag != tagV1 && tag != tagV0 {
		return "", "", false
	}
	n := int(data[3])
	if len(data) < 4+n {
		return "", "", false
	}
	return string(data[4 : 4+n]), string(data[4+n:]), true
}

var errNotObj = errors.New("k8setcd3: not an *Obj")
var errBadData = errors.New("k8setcd3: data does not decode")
var errBadRV = errors.New("k8setcd3: resource version does not parse")
var errNoList = errors.New("k8setcd3: lists are not supported")

// codec is the driver's runtime.Codec: the current encoding; it decodes either.
type codec struct{}

func (codec) Encode(obj runtime.Object, w io.Writer) error {
	o, ok := obj.(*Obj)
	if !ok {
		return errNotObj
	}
	_, err := w.Write(encodeObj(o))
	return err
}

func (codec) Identifier() runtime.Identifier {
	return runtime.Identifier("k8setcd3")
}

func (codec) Decode(data []byte, defaults *schema.GroupVersionKind, into runtime.Object) (runtime.Object, *schema.GroupVersionKind, error) {
	o, ok := into.(*Obj)
	if !ok {
		return nil, nil, errNotObj
	}
	name, val, ok := decodeObj(data)
	if !ok {
		return nil, nil, errBadData
	}
	o.Name = name
	o.Value = val
	return o, nil, nil
}

// parseRV parses a resource version string, the versioner's form of a number: empty for 0, its
// eight bytes (big-endian) otherwise.
func parseRV(s string) (uint64, error) {
	if len(s) == 0 {
		return 0, nil
	}
	if len(s) != 8 {
		return 0, errBadRV
	}
	var n uint64
	for i := 0; i < 8; i++ {
		n = n<<8 | uint64(s[i])
	}
	return n, nil
}

// versioner is the driver's storage.Versioner, on Obj's ResourceVersion.
type versioner struct{}

func (versioner) UpdateObject(obj runtime.Object, resourceVersion uint64) error {
	o, ok := obj.(*Obj)
	if !ok {
		return errNotObj
	}
	o.ResourceVersion = resourceVersion
	return nil
}

func (versioner) UpdateList(obj runtime.Object, resourceVersion uint64, continueValue string, remainingItemCount *int64) error {
	return errNoList
}

func (versioner) PrepareObjectForStorage(obj runtime.Object) error {
	o, ok := obj.(*Obj)
	if !ok {
		return errNotObj
	}
	o.ResourceVersion = 0
	return nil
}

func (versioner) ObjectResourceVersion(obj runtime.Object) (uint64, error) {
	o, ok := obj.(*Obj)
	if !ok {
		return 0, errNotObj
	}
	return o.ResourceVersion, nil
}

func (versioner) ParseResourceVersion(resourceVersion string) (uint64, error) {
	return parseRV(resourceVersion)
}

// decoder is the driver's etcd3.Decoder: the codec's decoding, at the key-value's revision.
type decoder struct{}

func (decoder) Decode(data []byte, objPtr runtime.Object, rev int64) error {
	o, ok := objPtr.(*Obj)
	if !ok {
		return errNotObj
	}
	name, val, ok := decodeObj(data)
	if !ok {
		return errBadData
	}
	o.Name = name
	o.Value = val
	o.ResourceVersion = uint64(rev)
	return nil
}

func (decoder) DecodeListItem(ctx context.Context, data []byte, rev uint64, newItemFunc func() runtime.Object) (runtime.Object, error) {
	return nil, errNoList
}

// identity is the driver's value.Transformer: no encryption at rest.
type identity struct{}

func (identity) TransformFromStorage(ctx context.Context, data []byte, dataCtx value.Context) ([]byte, bool, error) {
	return data, false, nil
}

func (identity) TransformToStorage(ctx context.Context, data []byte, dataCtx value.Context) ([]byte, error) {
	return data, nil
}

// noCompactor is the store's Compactor: no compaction (phase 0's configuration).
type noCompactor struct{}

func (noCompactor) CompactRevision() int64 {
	return 0
}

func newObj() runtime.Object {
	return &Obj{}
}

// ---------------------------------------------------------------------------------------------
// The operations

// The kinds of operation (Input.Kind).
const (
	KCreate = 0
	KDelete = 1
	KUpdate = 2
	KGet    = 3
)

// An Input is an operation on the key Key (a name: the store's key is "/objs/" + Key): a Create of
// the object with value Val; a Delete whose validateDeletion rejects a stored object of value
// Reject (none if empty); a GuaranteedUpdate whose tryUpdate rejects a stored object of value
// Reject, and otherwise sets the value Val, or, if NoOp, returns the object unchanged; or a Get,
// IgnoreNotFound as given. A plain value (porcupine's model decodes it purely).
type Input struct {
	Kind           int
	Key            string
	Val            string
	Reject         string
	NoOp           bool
	IgnoreNotFound bool
}

// The kinds of error an output carries (Output.Err).
const (
	// none: the call returned an object
	ENone = 0
	// a *storage.StorageError, "not found" (storage.ErrCodeKeyNotFound), with ErrKey and ErrRV
	ENotFound = 1
	// a *storage.StorageError, "key exists" (storage.ErrCodeKeyExists), with ErrKey and ErrRV
	EExists = 2
	// the callback's own error (errDeleteRejected, errUpdateRejected)
	ERejected = 3
	// any other error (the client's: the call may or may not have taken effect)
	EOther = 4
)

// An Output is a call's answer: the object it returned (its name, value and resource version),
// or its error.
type Output struct {
	Err    int
	ErrKey string
	ErrRV  int64
	Name   string
	Value  string
	RV     uint64
}

// The store's keys: Prefix + "/objs/" + name (the Model's Prefix and the store's resource
// prefix).
const (
	Prefix         = "/registry"
	ResourcePrefix = "/objs"
)

// storeKey is the key the store is called with for a name (the Model's item key).
func storeKey(name string) string {
	return ResourcePrefix + "/" + name
}

// The callbacks' errors (the correctness test's errDeleteRejected and errUpdateRejected).
var errDeleteRejected = errors.New("k8setcd3: deletion rejected")
var errUpdateRejected = errors.New("k8setcd3: update rejected")

// validateFor is a Delete's validateDeletion: it rejects an object of value reject.
func validateFor(reject string) storage.ValidateObjectFunc {
	return func(ctx context.Context, obj runtime.Object) error {
		o, ok := obj.(*Obj)
		if !ok {
			return errNotObj
		}
		if reject != "" && o.Value == reject {
			return errDeleteRejected
		}
		return nil
	}
}

// updated is a GuaranteedUpdate's result on the object o (a new object), or its error: the
// correctness test's randomUpdate, specialized (traffic.go: a copy, rejected on the drawn value,
// unchanged for a no-op, else the new value).
func updated(in Input, o *Obj) (*Obj, error) {
	if in.Reject != "" && o.Value == in.Reject {
		return nil, errUpdateRejected
	}
	c := *o
	if !in.NoOp {
		c.Value = in.Val
	}
	return &c, nil
}

// tryUpdateFor is a GuaranteedUpdate's tryUpdate (updated, with no TTL).
func tryUpdateFor(in Input) storage.UpdateFunc {
	return func(input runtime.Object, res storage.ResponseMeta) (runtime.Object, *uint64, error) {
		o, ok := input.(*Obj)
		if !ok {
			return nil, nil, errNotObj
		}
		r, err := updated(in, o)
		if err != nil {
			return nil, nil, err
		}
		return r, nil, nil
	}
}

// ---------------------------------------------------------------------------------------------
// The model (correctness.Model, specialized; with the canonical bit, D30g)

// An item of the model: its key (a name), its object (with its resource version set, as the
// Model's items), and whether the stored value is the store's current encoding of it (D30g).
type item struct {
	key   string
	obj   Obj
	canon bool
}

// A store: the items sorted by key and the resource version (the Model's Items and
// ResourceVersion; no compaction).
type mstore struct {
	items []item
	rv    uint64
}

// A configuration: a store and the failed writes that may still take effect.
type mcfg struct {
	st   mstore
	pend []Input
}

// A state is the set of configurations the history may have reached (no duplicates).
type state []mcfg

func lookup(items []item, k string) (item, bool) {
	for _, it := range items {
		if it.key == k {
			return it, true
		}
	}
	return item{}, false
}

// setItem returns items with k's item it (in key order; a new slice).
func setItem(items []item, it item) []item {
	out := make([]item, 0, len(items)+1)
	done := false
	for _, e := range items {
		if !done && it.key < e.key {
			out = append(out, it)
			done = true
		}
		if e.key == it.key {
			if !done {
				out = append(out, it)
				done = true
			}
			continue
		}
		out = append(out, e)
	}
	if !done {
		out = append(out, it)
	}
	return out
}

// delItem returns items without k's item (a new slice).
func delItem(items []item, k string) []item {
	out := make([]item, 0, len(items))
	for _, e := range items {
		if e.key != k {
			out = append(out, e)
		}
	}
	return out
}

func notFound(st mstore, key string) Output {
	return Output{Err: ENotFound, ErrKey: Prefix + storeKey(key), ErrRV: int64(st.rv)}
}

func objOut(o Obj) Output {
	return Output{Err: ENone, Name: o.Name, Value: o.Value, RV: o.ResourceVersion}
}

// mcreate is the Model's create: "key exists", or the object at the next resource version.
func mcreate(in Input, st mstore) (mstore, Output) {
	if _, ok := lookup(st.items, in.Key); ok {
		return st, Output{Err: EExists, ErrKey: Prefix + storeKey(in.Key), ErrRV: 0}
	}
	rv := st.rv + 1
	o := Obj{Name: in.Key, Value: in.Val, ResourceVersion: rv}
	return mstore{items: setItem(st.items, item{key: in.Key, obj: o, canon: true}), rv: rv}, objOut(o)
}

// mdelete is the Model's delete: "not found", validateDeletion's error on the stored object, or
// the item gone at the next resource version, answered with the object at that version.
func mdelete(in Input, st mstore) (mstore, Output) {
	it, ok := lookup(st.items, in.Key)
	if !ok {
		return st, notFound(st, in.Key)
	}
	c := it.obj
	if err := validateFor(in.Reject)(context.Background(), &c); err != nil {
		return st, Output{Err: ERejected}
	}
	rv := st.rv + 1
	o := it.obj
	o.ResourceVersion = rv
	return mstore{items: delItem(st.items, in.Key), rv: rv}, objOut(o)
}

// mupdate is the Model's update (no ignoreNotFound): "not found", tryUpdate's error on the
// stored object, the stored object if tryUpdate left it unchanged (its resource version aside)
// and the item is canonical (D30g; the Model: unchanged), or the result at the next resource
// version.
func mupdate(in Input, st mstore) (mstore, Output) {
	it, ok := lookup(st.items, in.Key)
	if !ok {
		return st, notFound(st, in.Key)
	}
	cur := it.obj
	r, err := updated(in, &cur)
	if err != nil {
		return st, Output{Err: ERejected}
	}
	if r.Name == it.obj.Name && r.Value == it.obj.Value && it.canon {
		return st, objOut(it.obj)
	}
	rv := st.rv + 1
	o := *r
	o.ResourceVersion = rv
	return mstore{items: setItem(st.items, item{key: in.Key, obj: o, canon: true}), rv: rv}, objOut(o)
}

// mget is the Model's get (no resource version): the stored object, the zero object for a
// missing key with IgnoreNotFound, or "not found".
func mget(in Input, st mstore) Output {
	it, ok := lookup(st.items, in.Key)
	if !ok {
		if in.IgnoreNotFound {
			return Output{Err: ENone}
		}
		return notFound(st, in.Key)
	}
	return objOut(it.obj)
}

// mstep is the Model's execute: the next store and the answer.
func mstep(in Input, st mstore) (mstore, Output) {
	if in.Kind == KCreate {
		return mcreate(in, st)
	}
	if in.Kind == KDelete {
		return mdelete(in, st)
	}
	if in.Kind == KUpdate {
		return mupdate(in, st)
	}
	return st, mget(in, st)
}

func isWrite(in Input) bool {
	return in.Kind != KGet
}

func outEqual(a, b Output) bool {
	return a.Err == b.Err && a.ErrKey == b.ErrKey && a.ErrRV == b.ErrRV && a.Name == b.Name &&
		a.Value == b.Value && a.RV == b.RV
}

func inputEqual(a, b Input) bool {
	return a == b
}

func storeEqual(a, b mstore) bool {
	if a.rv != b.rv || len(a.items) != len(b.items) {
		return false
	}
	for i := range a.items {
		if a.items[i] != b.items[i] {
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
	if out.Err == EOther {
		if isWrite(in) {
			pend := make([]Input, 0, len(c.pend)+1)
			pend = append(pend, in)
			pend = append(pend, c.pend...)
			return []mcfg{{st: c.st, pend: pend}}
		}
		return []mcfg{c}
	}
	st, o := mstep(in, c.st)
	if !outEqual(out, o) {
		return nil
	}
	return []mcfg{{st: st, pend: c.pend}}
}

// Model is the store as a porcupine model, from the store st0 (the seeded keys).
func Model(st0 mstore) porcupine.Model {
	return porcupine.Model{
		Init: func() any { return state{mcfg{st: st0}} },
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
// The workload (the correctness test's unary traffic, minimal)

func workloadKeys() []string {
	return []string{"a", "b", "c"}
}

func workloadVals() []string {
	return []string{"x", "y", "z"}
}

// pick returns n mod m and n / m.
func pick(n uint64, m uint64) (uint64, uint64) {
	return n % m, n / m
}

// genFrom is the operation Gen picks for the random number n (out of 100): a Create (25), a
// Delete (15), a GuaranteedUpdate (35) or a Get (25), of a random key and value; a quarter of the
// Deletes and updates reject a random value, a fifth of the updates are no-ops, half the Gets
// ignore "not found".
func genFrom(n uint64) Input {
	keys := workloadKeys()
	vals := workloadVals()
	w, n := pick(n, 100)
	ki, n := pick(n, uint64(len(keys)))
	vi, n := pick(n, uint64(len(vals)))
	rj, n := pick(n, 4)
	ri, n := pick(n, uint64(len(vals)))
	nop, n := pick(n, 5)
	ign, _ := pick(n, 2)
	k := keys[ki]
	v := vals[vi]
	reject := ""
	if rj == 0 {
		reject = vals[ri]
	}
	if w < 25 {
		return Input{Kind: KCreate, Key: k, Val: v}
	}
	if w < 40 {
		return Input{Kind: KDelete, Key: k, Reject: reject}
	}
	if w < 75 {
		return Input{Kind: KUpdate, Key: k, Val: v, Reject: reject, NoOp: nop == 0}
	}
	return Input{Kind: KGet, Key: k, IgnoreNotFound: ign == 0}
}

// Gen picks an operation at random (genFrom of a random number).
func Gen(id int) any {
	return genFrom(primitive.RandomUint64())
}

// ---------------------------------------------------------------------------------------------
// The calls

// errOut is a call's error as an output.
func errOut(err error) Output {
	if se, ok := err.(*storage.StorageError); ok {
		if se.Code == storage.ErrCodeKeyNotFound {
			return Output{Err: ENotFound, ErrKey: se.Key, ErrRV: se.ResourceVersion}
		}
		if se.Code == storage.ErrCodeKeyExists {
			return Output{Err: EExists, ErrKey: se.Key, ErrRV: se.ResourceVersion}
		}
	}
	if err == errDeleteRejected || err == errUpdateRejected {
		return Output{Err: ERejected}
	}
	return Output{Err: EOther}
}

// call runs one operation through the store s: its output (the object it left in a fresh out, or
// its error).
func call(s storage.Interface, in Input) Output {
	ctx := context.Background()
	out := &Obj{}
	var err error
	if in.Kind == KCreate {
		err = s.Create(ctx, storeKey(in.Key), &Obj{Name: in.Key, Value: in.Val}, out, 0)
	} else if in.Kind == KDelete {
		err = s.Delete(ctx, storeKey(in.Key), out, nil, validateFor(in.Reject), nil,
			storage.DeleteOptions{})
	} else if in.Kind == KUpdate {
		err = s.GuaranteedUpdate(ctx, storeKey(in.Key), out, false, nil, tryUpdateFor(in), nil)
	} else {
		err = s.Get(ctx, storeKey(in.Key), storage.GetOptions{IgnoreNotFound: in.IgnoreNotFound},
			out)
	}
	if err != nil {
		return errOut(err)
	}
	return objOut(*out)
}

// Apply runs one operation through the store s, resolving a prophecy with the output's numeric
// fields (its error kind, its error's resource version, its object's resource version): what the
// proof's linearization point compares the store's answer at a read with, the rest of the output
// following from them.
func Apply(s storage.Interface, input any) any {
	in := input.(Input)
	p := primitive.NewProph()
	out := call(s, in)
	p.ResolveU64(uint64(out.Err))
	p.ResolveU64(uint64(out.ErrRV))
	p.ResolveU64(out.RV)
	return out
}

// Check runs lintest.Run of clients concurrent clients of the store s, each running ops
// operations, and returns porcupine's verdict against Model from the store st0.
func Check(s storage.Interface, st0 mstore, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	apply := func(input any) any { return Apply(s, input) }
	return lintest.Run(Model(st0), apply, Gen, lintest.CounterClock(), clients, ops, timeout)
}

// The keys seeded in the older encoding before the traffic, and their values.
func seedKeys() []string {
	return []string{"a", "b"}
}

// seed writes each seed key's object in the older encoding directly through the client cli
// (non-canonical data, as a store with an older codec left: D30g), and returns the model's store
// after them, or false if a put failed.
func seed(cli *clientv3.Client) (mstore, bool) {
	st := mstore{rv: 1}
	for _, k := range seedKeys() {
		resp, err := cli.Put(context.Background(), Prefix+storeKey(k), string(encodeV0(k, "x")))
		if err != nil {
			return mstore{}, false
		}
		rv := uint64(resp.Header.Revision)
		o := Obj{Name: k, Value: "x", ResourceVersion: rv}
		st = mstore{items: setItem(st.items, item{key: k, obj: o, canon: false}), rv: rv}
	}
	return st, true
}

// The client address: the string net.Listen is given is the client's endpoint, verbatim (a plain
// host:port, no scheme). Not the other examples', so that their tests can run at once.
const clientAddr = "127.0.0.1:23896"

// Main starts one member of a new cluster (as examples/linkvtxn's Main does), connects a
// kubernetes client configured for one attempt per call, seeds the keys, makes the store and runs
// Check; it panics if porcupine finds the history illegal. An error from a step before Check ends
// Main without a check.
func Main(clients int, ops int) porcupine.CheckResult {
	lg := zap.NewNop()
	peer := types.URLs{{Scheme: "http", Host: "127.0.0.1:23906"}}
	cfg := config.ServerConfig{
		Name:                "k8setcd3",
		DataDir:             "k8setcd3.etcd",
		InitialPeerURLsMap:  types.URLsMap{"k8setcd3": peer},
		PeerURLs:            peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: clientAddr}},
		InitialClusterToken: "k8setcd3",
		NewCluster:          true,
		TickMs:              100,
		ElectionTicks:       10,
		// etcd's default snapshot count; the catch-up entries past the theorem's step bound (as
		// examples/linkv's)
		SnapshotCount:          etcdserver.DefaultSnapshotCount,
		SnapshotCatchUpEntries: 1 << 48,
		MaxTxnOps:              128,
		MaxRequestBytes:        1536 * 1024,
		Logger:                 lg,
		ServerFeatureGate:      features.NewDefaultServerFeatureGate("k8setcd3", lg),
	}
	srv, err := etcdserver.NewServer(cfg)
	if err != nil {
		return porcupine.Unknown
	}
	srv.Start()

	gs := v3rpc.Server(srv, nil, nil)
	l, err := net.Listen("tcp", clientAddr)
	if err != nil {
		return porcupine.Unknown
	}
	go gs.Serve(l)

	// One attempt per call (MaxUnaryRetries: 1): a write is sent at most once, so the server
	// applies it at most once.
	kc, err := kubernetes.New(clientv3.Config{
		Endpoints:       []string{clientAddr},
		Logger:          lg,
		MaxUnaryRetries: 1,
	})
	if err != nil {
		return porcupine.Unknown
	}
	st0, ok := seed(kc.Client)
	if !ok {
		return porcupine.Unknown
	}
	s, err := etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix,
		schema.GroupResource{Resource: "objs"}, identity{}, etcd3.NewDefaultLeaseManagerConfig(),
		decoder{}, versioner{})
	if err != nil {
		return porcupine.Unknown
	}
	r := Check(s, st0, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("k8setcd3: porcupine found the history not linearizable")
	}
	return r
}
