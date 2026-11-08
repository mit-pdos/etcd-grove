// Package etcd3 is the lintest driver instantiated with Kubernetes' etcd3 storage backend
// (k8s.io/apiserver/pkg/storage/etcd3, over this repository's etcd fork; notes/k8s-etcd3-plan.md,
// phase 6): one etcd member started in-process (as examples/etcd/txnlin does), a kubernetes client
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
// As examples/etcd/txnlin's model, Model runs over configurations with pending failed writes: a
// call that returned no error took effect at once and answered as the model; a failed write may
// take effect at any later time, or never; a failed read constrains nothing.
//
// The traffic is the unary traffic of Kubernetes' storage correctness test
// (test/integration/apiserver/storage/traffic.go, TestCorrectness's requestDistribution) without
// lists (notes/k8s-etcd3-plan.md, stage 7b): Creates (a new UID, no resource version or TTL),
// Deletes and GuaranteedUpdates with UID and resource-version preconditions and a cached object
// (the client's last answer, as the test's), updates with ignoreNotFound, the test's rejecting
// validateDeletion and tryUpdate (a sentinel error when the stored object's value is the one
// drawn) and its no-op updates, and Gets with IgnoreNotFound and a minimum resource version (empty,
// 0, 1, the cached object's, or relative to it). Main panics if porcupine finds the history not
// linearizable; the theorem to prove is that it does not.
package etcd3

import (
	"context"
	"errors"
	"io"
	"strings"
	"sync"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"

	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/fields"
	"k8s.io/apimachinery/pkg/labels"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/apiserver/pkg/storage"
	"k8s.io/apiserver/pkg/storage/etcd3"
	"k8s.io/apiserver/pkg/storage/value"
	utilfeature "k8s.io/apiserver/pkg/util/feature"

	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
)

// ---------------------------------------------------------------------------------------------
// The driver's objects, codec, versioner, decoder and transformer

// An Obj is the driver's object: its namespace and name (the key it is stored at is
// "<namespace>/<name>"), its UID (Kubernetes' objects' identity across a delete and a re-create: a
// Create's is drawn at random), a value, a node and an app label (the test's Pods' spec.nodeName
// and label "app", "" for none: what the test's selectors select on), and its resource version (0
// for none). Kubernetes' objects keep the resource version as a decimal string; the driver keeps
// the number, and its versioner's string form of it is rvString's.
type Obj struct {
	Namespace       string
	Name            string
	UID             string
	Value           string
	Node            string
	App             string
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

// An ObjList is the driver's list object (GetList's listObj): its items, and the list's resource
// version, continue token and remaining item count (ListMeta's, set by the versioner's
// UpdateList).
type ObjList struct {
	Items              []Obj
	ResourceVersion    uint64
	Continue           string
	RemainingItemCount *int64
}

// GetObjectKind is runtime.Object's: the driver's lists carry no kind.
func (l *ObjList) GetObjectKind() schema.ObjectKind {
	return schema.EmptyObjectKind
}

// DeepCopyObject is runtime.Object's: a copy (of the items and the count too).
func (l *ObjList) DeepCopyObject() runtime.Object {
	c := *l
	c.Items = append([]Obj{}, l.Items...)
	if l.RemainingItemCount != nil {
		n := *l.RemainingItemCount
		c.RemainingItemCount = &n
	}
	return &c
}

// The current encoding's tag, and the older one the codec still decodes.
const (
	tagV1 = "v1:"
	tagV0 = "v0:"
)

// putField appends a field, its length (one byte; fields are shorter than 256 bytes) and its bytes.
func putField(out []byte, f string) []byte {
	out = append(out, byte(len(f)))
	return append(out, []byte(f)...)
}

// encodeWith is the encoding of an object's fields (not its resource version) under the tag tag:
// the tag, the namespace, name, UID, node and app as length-prefixed fields (putField), and the
// value.
func encodeWith(tag string, o Obj) []byte {
	out := []byte(tag)
	out = putField(out, o.Namespace)
	out = putField(out, o.Name)
	out = putField(out, o.UID)
	out = putField(out, o.Node)
	out = putField(out, o.App)
	return append(out, []byte(o.Value)...)
}

// encodeObj is the current encoding of an object.
func encodeObj(o *Obj) []byte {
	return encodeWith(tagV1, *o)
}

// encodeV0 is the older encoding. The driver seeds some keys with it.
func encodeV0(o Obj) []byte {
	return encodeWith(tagV0, o)
}

// getField reads a length-prefixed field at i: the field and the index after it, or false.
func getField(data []byte, i int) (string, int, bool) {
	if len(data) < i+1 {
		return "", 0, false
	}
	n := int(data[i])
	if len(data) < i+1+n {
		return "", 0, false
	}
	return string(data[i+1 : i+1+n]), i + 1 + n, true
}

// decodeObj decodes either encoding: the object's fields (its resource version 0), or false.
func decodeObj(data []byte) (Obj, bool) {
	if len(data) < 3 {
		return Obj{}, false
	}
	tag := string(data[:3])
	if tag != tagV1 && tag != tagV0 {
		return Obj{}, false
	}
	ns, i, ok := getField(data, 3)
	if !ok {
		return Obj{}, false
	}
	name, i, ok := getField(data, i)
	if !ok {
		return Obj{}, false
	}
	uid, i, ok := getField(data, i)
	if !ok {
		return Obj{}, false
	}
	node, i, ok := getField(data, i)
	if !ok {
		return Obj{}, false
	}
	app, i, ok := getField(data, i)
	if !ok {
		return Obj{}, false
	}
	return Obj{Namespace: ns, Name: name, UID: uid, Value: string(data[i:]), Node: node, App: app}, true
}

var errNotObj = errors.New("k8setcd3: not an *Obj")
var errBadData = errors.New("k8setcd3: data does not decode")
var errBadRV = errors.New("k8setcd3: resource version does not parse")

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
	d, ok := decodeObj(data)
	if !ok {
		return nil, nil, errBadData
	}
	d.ResourceVersion = o.ResourceVersion
	*o = d
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

// rvBytes is the eight bytes (big-endian) of n.
func rvBytes(n uint64) string {
	b := make([]byte, 8)
	for i := 0; i < 8; i++ {
		b[i] = byte(n >> (56 - 8*uint64(i)))
	}
	return string(b)
}

// rvString is the versioner's string form of a resource version, which parseRV parses: empty for
// 0, its eight bytes otherwise.
func rvString(n uint64) string {
	if n == 0 {
		return ""
	}
	return rvBytes(n)
}

// The metav1.Object interface, which Preconditions.Check reads through meta.Accessor: the
// namespace, name, UID, labels and resource version (as the versioner's string) are the object's;
// the rest of the metadata is empty and its setters do nothing.

func (o *Obj) GetNamespace() string                                       { return o.Namespace }
func (o *Obj) SetNamespace(namespace string)                              { o.Namespace = namespace }
func (o *Obj) GetName() string                                            { return o.Name }
func (o *Obj) SetName(name string)                                        { o.Name = name }
func (o *Obj) GetGenerateName() string                                    { return "" }
func (o *Obj) SetGenerateName(name string)                                {}
func (o *Obj) GetUID() types.UID                                          { return types.UID(o.UID) }
func (o *Obj) SetUID(uid types.UID)                                       { o.UID = string(uid) }
func (o *Obj) GetResourceVersion() string                                 { return rvString(o.ResourceVersion) }
func (o *Obj) SetResourceVersion(version string)                          {}
func (o *Obj) GetGeneration() int64                                       { return 0 }
func (o *Obj) SetGeneration(generation int64)                             {}
func (o *Obj) GetSelfLink() string                                        { return "" }
func (o *Obj) SetSelfLink(selfLink string)                                {}
func (o *Obj) GetCreationTimestamp() metav1.Time                          { return metav1.Time{} }
func (o *Obj) SetCreationTimestamp(timestamp metav1.Time)                 {}
func (o *Obj) GetDeletionTimestamp() *metav1.Time                         { return nil }
func (o *Obj) SetDeletionTimestamp(timestamp *metav1.Time)                {}
func (o *Obj) GetDeletionGracePeriodSeconds() *int64                      { return nil }
func (o *Obj) SetDeletionGracePeriodSeconds(s *int64)                     {}
func (o *Obj) GetLabels() map[string]string                               { return objLabels(*o) }
func (o *Obj) SetLabels(labels map[string]string)                         {}
func (o *Obj) GetAnnotations() map[string]string                          { return nil }
func (o *Obj) SetAnnotations(annotations map[string]string)               {}
func (o *Obj) GetFinalizers() []string                                    { return nil }
func (o *Obj) SetFinalizers(finalizers []string)                          {}
func (o *Obj) GetOwnerReferences() []metav1.OwnerReference                { return nil }
func (o *Obj) SetOwnerReferences(refs []metav1.OwnerReference)            {}
func (o *Obj) GetManagedFields() []metav1.ManagedFieldsEntry              { return nil }
func (o *Obj) SetManagedFields(managedFields []metav1.ManagedFieldsEntry) {}

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
	l, ok := obj.(*ObjList)
	if !ok {
		return errNotObj
	}
	l.ResourceVersion = resourceVersion
	l.Continue = continueValue
	l.RemainingItemCount = remainingItemCount
	return nil
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
	d, ok := decodeObj(data)
	if !ok {
		return errBadData
	}
	d.ResourceVersion = uint64(rev)
	*o = d
	return nil
}

// DecodeListItem is the codec's decoding of a list's item into a new object (newItemFunc's), at
// the key-value's revision.
func (decoder) DecodeListItem(ctx context.Context, data []byte, rev uint64, newItemFunc func() runtime.Object) (runtime.Object, error) {
	obj := newItemFunc()
	o, ok := obj.(*Obj)
	if !ok {
		return nil, errNotObj
	}
	d, ok := decodeObj(data)
	if !ok {
		return nil, errBadData
	}
	d.ResourceVersion = rev
	*o = d
	return o, nil
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
	KList   = 4
)

// The resource version matches of a list (Input.Match: metav1.ResourceVersionMatch's "",
// NotOlderThan and Exact).
const (
	MLegacy       = 0
	MNotOlderThan = 1
	MExact        = 2
)

// The field selectors of a list (Input.Field: the test's pickPredicate): everything,
// metadata.name, metadata.namespace, spec.nodeName (a non-empty node), spec.nodeName "", and
// metadata.namespace and spec.nodeName together.
const (
	FEverything = 0
	FByName     = 1
	FByNS       = 2
	FByNode     = 3
	FEmptyNode  = 4
	FCombined   = 5
)

// An Input is client Client's operation. A write or a Get is on the key Key ("<namespace>/<name>";
// the store's key is "/objs/" + Key):
//   - a Create of the object with UID UID, value Val, node Node and app App;
//   - a Delete whose validateDeletion rejects a stored object on node Reject (if HasReject);
//   - a GuaranteedUpdate whose tryUpdate rejects a stored object on node Reject (if HasReject),
//     and otherwise sets the value Val, node Node and app App (on the zero object, also the
//     namespace and name of Key), or, if NoOp, returns the object unchanged, with ignoreNotFound
//     IgnoreNotFound;
//   - a Get, IgnoreNotFound as given, with the minimum resource version MinRV (the versioner's
//     string; empty for none).
//
// A Delete and an update have the preconditions PreUID (if HasPreUID) and PreRV (the versioner's
// string, if HasPreRV), and the cached object Cached (if UseCached), a copy of the client's last
// answer. A List is of the store key ListKey (recursive if Recursive), with the resource version
// MinRV and the match Match, the field selector Field (on the namespace SelNS, name SelName or node
// SelNode it names), the label selector app = SelApp (everything if SelApp is empty) and the limit
// Limit. A plain value (porcupine's model decodes it purely).
type Input struct {
	Kind           int
	Key            string
	Val            string
	Node           string
	App            string
	HasReject      bool
	Reject         string
	NoOp           bool
	IgnoreNotFound bool
	UID            string
	HasPreUID      bool
	PreUID         string
	HasPreRV       bool
	PreRV          string
	UseCached      bool
	Cached         Obj
	MinRV          string
	ListKey        string
	Recursive      bool
	Match          int
	Field          int
	SelNS          string
	SelName        string
	SelNode        string
	SelApp         string
	Limit          int64
	Client         int
}

// The kinds of error an output carries (Output.Err).
const (
	// none: the call returned an object (a list, for a List)
	ENone = 0
	// a *storage.StorageError, "not found" (storage.ErrCodeKeyNotFound), with ErrKey and ErrRV
	ENotFound = 1
	// a *storage.StorageError, "key exists" (storage.ErrCodeKeyExists), with ErrKey and ErrRV
	EExists = 2
	// the callback's own error (errDeleteRejected, errUpdateRejected)
	ERejected = 3
	// any other error (the client's: the call may or may not have taken effect)
	EOther = 4
	// a *storage.StorageError, "invalid object" (storage.ErrCodeInvalidObj: a failed
	// precondition), with ErrKey
	EInvalid = 5
	// a resource version above the store's (storage.IsTooLargeResourceVersion: a Get's minimum
	// above the revision read, or a List's resource version above it, ErrFutureRev). The client's
	// own errors are not *apierrors.StatusErrors (notes/k8s-etcd3-plan.md, 7b T2 (c)).
	ETooLarge = 6
)

// An Output is a call's answer: the object it returned (its namespace, name, UID, value, node, app
// and resource version), the list it returned (its items, its resource version ListRV, its
// continue token Continue, and its remaining item count Remaining if HasRemaining), or its error.
type Output struct {
	Err          int
	ErrKey       string
	ErrRV        int64
	Namespace    string
	Name         string
	UID          string
	Value        string
	Node         string
	App          string
	RV           uint64
	Items        []Obj
	ListRV       uint64
	Continue     string
	HasRemaining bool
	Remaining    int64
}

// The store's keys: Prefix + "/objs/" + key (the Model's Prefix and the store's resource prefix).
const (
	Prefix         = "/registry"
	ResourcePrefix = "/objs"
)

// storeKey is the key the store is called with for a key "<namespace>/<name>" (the Model's item
// key).
func storeKey(key string) string {
	return ResourcePrefix + "/" + key
}

// splitKey splits a key "<namespace>/<name>" at its first "/": the namespace and the name (the
// key and "" if it has no "/"; strings.Cut's answer, as a loop: Perennial has no model of Cut).
func splitKey(key string) (string, string) {
	for i := 0; i < len(key); i++ {
		if key[i] == '/' {
			return key[:i], key[i+1:]
		}
	}
	return key, ""
}

// objLabels is an object's labels: app, if it has one.
func objLabels(o Obj) map[string]string {
	if o.App == "" {
		return nil
	}
	return map[string]string{"app": o.App}
}

// The callbacks' errors (the correctness test's errDeleteRejected and errUpdateRejected).
var errDeleteRejected = errors.New("k8setcd3: deletion rejected")
var errUpdateRejected = errors.New("k8setcd3: update rejected")

// validateFor is a Delete's validateDeletion: it rejects an object on the node reject, if rejects.
func validateFor(rejects bool, reject string) storage.ValidateObjectFunc {
	return func(ctx context.Context, obj runtime.Object) error {
		o, ok := obj.(*Obj)
		if !ok {
			return errNotObj
		}
		if rejects && o.Node == reject {
			return errDeleteRejected
		}
		return nil
	}
}

// updated is a GuaranteedUpdate's result on the object o (a new object), or its error: the
// correctness test's randomUpdate, specialized (traffic.go: rejected on the drawn node, unchanged
// for a no-op, else the new value, node and app; the zero object, met with ignoreNotFound, becomes
// the key's object, as the test's validPod, without a UID).
func updated(in Input, o *Obj) (*Obj, error) {
	if in.HasReject && o.Node == in.Reject {
		return nil, errUpdateRejected
	}
	c := *o
	if !in.NoOp {
		if c.Name == "" {
			c.Namespace, c.Name = splitKey(in.Key)
		}
		c.Value = in.Val
		c.Node = in.Node
		c.App = in.App
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
// The selectors (the test's pickPredicate, as the driver's own labels.Selector and fields.Selector)

// A fieldSel is a conjunction of n (0 to 2) field equalities f1 = v1 and f2 = v2: everything for
// n = 0 (fields.Everything, OneTermEqualSelector, AndSelectors of two).
type fieldSel struct {
	n  int
	f1 string
	v1 string
	f2 string
	v2 string
}

func (s fieldSel) Matches(f fields.Fields) bool {
	if s.n >= 1 && f.Get(s.f1) != s.v1 {
		return false
	}
	if s.n >= 2 && f.Get(s.f2) != s.v2 {
		return false
	}
	return true
}

func (s fieldSel) Empty() bool { return s.n == 0 }

func (s fieldSel) RequiresExactMatch(field string) (string, bool) {
	if s.n >= 1 && s.f1 == field {
		return s.v1, true
	}
	if s.n >= 2 && s.f2 == field {
		return s.v2, true
	}
	return "", false
}

func (s fieldSel) Transform(fn fields.TransformFunc) (fields.Selector, error) { return s, nil }
func (s fieldSel) Requirements() fields.Requirements                          { return nil }
func (s fieldSel) String() string                                             { return s.f1 + "=" + s.v1 + "," + s.f2 + "=" + s.v2 }
func (s fieldSel) DeepCopySelector() fields.Selector                          { return s }

// A labelSel is the label selector app = app, or everything if all (labels.Everything,
// labels.SelectorFromSet of one label).
type labelSel struct {
	all bool
	app string
}

func (s labelSel) Matches(l labels.Labels) bool {
	return s.all || (l.Has("app") && l.Get("app") == s.app)
}

func (s labelSel) Empty() bool                                 { return s.all }
func (s labelSel) String() string                              { return "app=" + s.app }
func (s labelSel) Add(r ...labels.Requirement) labels.Selector { return s }
func (s labelSel) Requirements() (labels.Requirements, bool)   { return nil, false }
func (s labelSel) DeepCopySelector() labels.Selector           { return s }
func (s labelSel) RequiresExactMatch(label string) (string, bool) {
	if !s.all && label == "app" {
		return s.app, true
	}
	return "", false
}

// getAttrs is the predicates' GetAttrs (the test's registrypod.GetAttrs, for the driver's object):
// the labels and the fields metadata.name, metadata.namespace and spec.nodeName. Total on Obj (a
// Matches error would silently drop the item).
func getAttrs(obj runtime.Object) (labels.Set, fields.Set, error) {
	o, ok := obj.(*Obj)
	if !ok {
		return nil, nil, errNotObj
	}
	return labels.Set(objLabels(*o)), fields.Set{"metadata.name": o.Name,
		"metadata.namespace": o.Namespace, "spec.nodeName": o.Node}, nil
}

// fieldSelFor is a List's field selector.
func fieldSelFor(in Input) fieldSel {
	if in.Field == FByName {
		return fieldSel{n: 1, f1: "metadata.name", v1: in.SelName}
	}
	if in.Field == FByNS {
		return fieldSel{n: 1, f1: "metadata.namespace", v1: in.SelNS}
	}
	if in.Field == FByNode {
		return fieldSel{n: 1, f1: "spec.nodeName", v1: in.SelNode}
	}
	if in.Field == FEmptyNode {
		return fieldSel{n: 1, f1: "spec.nodeName", v1: ""}
	}
	if in.Field == FCombined {
		return fieldSel{n: 2, f1: "metadata.namespace", v1: in.SelNS, f2: "spec.nodeName", v2: in.SelNode}
	}
	return fieldSel{}
}

// predicate is a List's selection predicate: its selectors, getAttrs and its limit.
func predicate(in Input) storage.SelectionPredicate {
	return storage.SelectionPredicate{
		Label:    labelSel{all: in.SelApp == "", app: in.SelApp},
		Field:    fieldSelFor(in),
		GetAttrs: getAttrs,
		Limit:    in.Limit,
	}
}

// matchOpt is a List's metav1.ResourceVersionMatch.
func matchOpt(in Input) metav1.ResourceVersionMatch {
	if in.Match == MNotOlderThan {
		return metav1.ResourceVersionMatchNotOlderThan
	}
	if in.Match == MExact {
		return metav1.ResourceVersionMatchExact
	}
	return ""
}

// listOptions is a List's storage.ListOptions.
func listOptions(in Input) storage.ListOptions {
	return storage.ListOptions{ResourceVersion: in.MinRV, ResourceVersionMatch: matchOpt(in),
		Predicate: predicate(in), Recursive: in.Recursive}
}

// ---------------------------------------------------------------------------------------------
// The model (correctness.Model, specialized; with the canonical bit, D30g)

// An item of the model: its key ("<namespace>/<name>"), its object (with its resource version set, as the
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

// A configuration: a store, the failed writes that may still take effect, and the store's
// history: the store at each revision R, 1 <= R <= st.rv (histLen(hist) = st.rv; histAt(hist, R)
// is the store at R); a write that bumps the revision appends its store.
type mcfg struct {
	st   mstore
	pend []Input
	hist *hnode
}

// An hnode is a history, persistent (shared between the configurations and porcupine's cached
// states that extend it, never modified): its last store st, its length n (st's revision), and the
// history before it.
type hnode struct {
	st   mstore
	n    uint64
	prev *hnode
}

// histLen is a history's length.
func histLen(h *hnode) uint64 {
	if h == nil {
		return 0
	}
	return h.n
}

// appendHist is hist with s appended (a new node; hist is shared, not changed).
func appendHist(h *hnode, s mstore) *hnode {
	return &hnode{st: s, n: histLen(h) + 1, prev: h}
}

// histOf is the history of the stores ss (ss[R-1] the store at revision R).
func histOf(ss []mstore) *hnode {
	var h *hnode
	for _, s := range ss {
		h = appendHist(h, s)
	}
	return h
}

// histAt is the store at revision r, 1 <= r <= histLen(h).
func histAt(h *hnode, r uint64) mstore {
	for h != nil && h.n > r {
		h = h.prev
	}
	if h == nil {
		return mstore{}
	}
	return h.st
}

// histEqual says whether two histories have equal stores (a shared tail is equal).
func histEqual(a *hnode, b *hnode) bool {
	if histLen(a) != histLen(b) {
		return false
	}
	for a != b {
		if !storeEqual(a.st, b.st) {
			return false
		}
		a, b = a.prev, b.prev
	}
	return true
}

// advance is c's configuration after its store steps to st: its history grows iff the revision
// does.
func advance(c mcfg, st mstore, pend []Input) mcfg {
	if st.rv != c.st.rv {
		return mcfg{st: st, pend: pend, hist: appendHist(c.hist, st)}
	}
	return mcfg{st: st, pend: pend, hist: c.hist}
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

func invalidObj(key string) Output {
	return Output{Err: EInvalid, ErrKey: Prefix + storeKey(key)}
}

func objOut(o Obj) Output {
	return Output{Err: ENone, Namespace: o.Namespace, Name: o.Name, UID: o.UID, Value: o.Value,
		Node: o.Node, App: o.App, RV: o.ResourceVersion}
}

// objOf is an answer's object (the client's cached object).
func objOf(out Output) Obj {
	return Obj{Namespace: out.Namespace, Name: out.Name, UID: out.UID, Value: out.Value,
		Node: out.Node, App: out.App, ResourceVersion: out.RV}
}

// preOk is the Model's preconditions.Check on the object o: the UID and the resource version (as
// the versioner's string), where given, are o's.
func preOk(in Input, o Obj) bool {
	if in.HasPreUID && in.PreUID != o.UID {
		return false
	}
	if in.HasPreRV && in.PreRV != rvString(o.ResourceVersion) {
		return false
	}
	return true
}

// sameObj says whether two objects are equal but for their resource versions.
func sameObj(a Obj, b Obj) bool {
	return a.Namespace == b.Namespace && a.Name == b.Name && a.UID == b.UID && a.Value == b.Value &&
		a.Node == b.Node && a.App == b.App
}

// mcreate is the Model's create: "key exists", or the object at the next resource version.
func mcreate(in Input, st mstore) (mstore, Output) {
	if _, ok := lookup(st.items, in.Key); ok {
		return st, Output{Err: EExists, ErrKey: Prefix + storeKey(in.Key), ErrRV: 0}
	}
	rv := st.rv + 1
	ns, name := splitKey(in.Key)
	o := Obj{Namespace: ns, Name: name, UID: in.UID, Value: in.Val, Node: in.Node, App: in.App,
		ResourceVersion: rv}
	return mstore{items: setItem(st.items, item{key: in.Key, obj: o, canon: true}), rv: rv}, objOut(o)
}

// mdelete is the Model's delete: "not found", a failed precondition on the stored object,
// validateDeletion's error on it, or the item gone at the next resource version, answered with
// the object at that version.
func mdelete(in Input, st mstore) (mstore, Output) {
	it, ok := lookup(st.items, in.Key)
	if !ok {
		return st, notFound(st, in.Key)
	}
	if !preOk(in, it.obj) {
		return st, invalidObj(in.Key)
	}
	c := it.obj
	if err := validateFor(in.HasReject, in.Reject)(context.Background(), &c); err != nil {
		return st, Output{Err: ERejected}
	}
	rv := st.rv + 1
	o := it.obj
	o.ResourceVersion = rv
	return mstore{items: delItem(st.items, in.Key), rv: rv}, objOut(o)
}

// mupdate is the Model's update: from the stored object, or the zero object at resource version
// 0 for a missing key with ignoreNotFound ("not found" without): a failed precondition,
// tryUpdate's error, the stored object if tryUpdate left it unchanged (its resource version
// aside) and the item is canonical (D30g; the Model: unchanged), or the result at the next
// resource version.
func mupdate(in Input, st mstore) (mstore, Output) {
	it, ok := lookup(st.items, in.Key)
	cur := Obj{}
	if ok {
		cur = it.obj
	} else if !in.IgnoreNotFound {
		return st, notFound(st, in.Key)
	}
	if !preOk(in, cur) {
		return st, invalidObj(in.Key)
	}
	r, err := updated(in, &cur)
	if err != nil {
		return st, Output{Err: ERejected}
	}
	if ok && sameObj(*r, it.obj) && it.canon {
		return st, objOut(it.obj)
	}
	rv := st.rv + 1
	o := *r
	o.ResourceVersion = rv
	return mstore{items: setItem(st.items, item{key: in.Key, obj: o, canon: true}), rv: rv}, objOut(o)
}

// mget is the Model's get: too-large if the minimum resource version is above the store's, an
// EOther if it does not parse (the versioner's error; the traffic sends none), the stored object,
// the zero object for a missing key with IgnoreNotFound, or "not found".
func mget(in Input, st mstore) Output {
	req, err := parseRV(in.MinRV)
	if err != nil {
		return Output{Err: EOther}
	}
	if req > st.rv {
		return Output{Err: ETooLarge}
	}
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

// isWrite says whether an operation is a write (a failed one may still take effect).
func isWrite(in Input) bool {
	return in.Kind == KCreate || in.Kind == KDelete || in.Kind == KUpdate
}

// pastRead says whether a List reads at its resource version, a past revision
// (storage.ValidateListOptions: Exact, and the legacy match recursive with a limit and a non-zero
// resource version), not at the latest one; req is its resource version.
func pastRead(in Input, req uint64) bool {
	if in.MinRV == "" || req == 0 {
		return false
	}
	return in.Match == MExact || (in.Match == MLegacy && in.Recursive && in.Limit > 0)
}

// keyInScope is the Model's: whether the store key k is selected by a list of key (exact if not
// recursive; with the "/" boundary if recursive: "/a" selects "/a/x", not "/ab").
func keyInScope(key string, recursive bool, k string) bool {
	if !recursive {
		return k == key
	}
	return strings.HasPrefix(k, strings.TrimSuffix(key, "/")+"/")
}

// mlist is the Model's list on a configuration: too-large if the resource version is above the
// store's; else, from the store at the resource version for a past read (pastRead) and the
// current store otherwise, the Model's loop: the keys in scope in order, totalCount of them, the
// first Limit matching items (all if Limit is 0), hasMore iff a key in scope follows the
// Limit-th match, and the continue token and remaining count of storage.PrepareContinueToken (the
// store's), at the list's resource version (the resource version read).
func mlist(in Input, c mcfg) Output {
	req, err := parseRV(in.MinRV)
	if err != nil {
		return Output{Err: EOther}
	}
	if req > c.st.rv {
		return Output{Err: ETooLarge}
	}
	st := c.st
	if pastRead(in, req) {
		st = histAt(c.hist, req)
	}
	pred := predicate(in)
	var items []Obj
	lastKey := ""
	hasMore := false
	var total int64
	for _, it := range st.items {
		k := storeKey(it.key)
		if !keyInScope(in.ListKey, in.Recursive, k) {
			continue
		}
		total++
		if in.Limit > 0 && int64(len(items)) >= in.Limit {
			hasMore = true
			continue
		}
		o := it.obj
		if ok, err := pred.Matches(&o); err == nil && ok {
			items = append(items, o)
			lastKey = k
		}
	}
	prepared, err := storage.PrepareKey(ResourcePrefix, in.ListKey, in.Recursive)
	if err != nil {
		return Output{Err: EOther}
	}
	cont, rem, err := storage.PrepareContinueToken(Prefix+lastKey, Prefix+prepared, int64(st.rv), total,
		hasMore, listOptions(in))
	if err != nil {
		return Output{Err: EOther}
	}
	out := Output{Err: ENone, Items: items, ListRV: st.rv, Continue: cont}
	if rem != nil {
		out.HasRemaining = true
		out.Remaining = *rem
	}
	return out
}

func outEqual(a, b Output) bool {
	if a.Err != b.Err || a.ErrKey != b.ErrKey || a.ErrRV != b.ErrRV || a.Namespace != b.Namespace ||
		a.Name != b.Name || a.UID != b.UID || a.Value != b.Value || a.Node != b.Node ||
		a.App != b.App || a.RV != b.RV || a.ListRV != b.ListRV || a.Continue != b.Continue ||
		a.HasRemaining != b.HasRemaining || a.Remaining != b.Remaining || len(a.Items) != len(b.Items) {
		return false
	}
	for i := range a.Items {
		if a.Items[i] != b.Items[i] {
			return false
		}
	}
	return true
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
	if !storeEqual(a.st, b.st) || len(a.pend) != len(b.pend) || !histEqual(a.hist, b.hist) {
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
			work = append(work, advance(c, st, removeAt(c.pend, i)))
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
			return []mcfg{{st: c.st, pend: pend, hist: c.hist}}
		}
		return []mcfg{c}
	}
	if in.Kind == KList {
		if !outEqual(out, mlist(in, c)) {
			return nil
		}
		return []mcfg{c}
	}
	st, o := mstep(in, c.st)
	if !outEqual(out, o) {
		return nil
	}
	return []mcfg{advance(c, st, c.pend)}
}

// Model is the store as a porcupine model, from the store st0 (the seeded keys) with its history
// h0 (len(h0) = st0.rv).
func Model(st0 mstore, h0 []mstore) porcupine.Model {
	return porcupine.Model{
		Init: func() any { return state{mcfg{st: st0, hist: histOf(h0)}} },
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
// The workload (the correctness test's unary traffic)

// workloadKeys are the test's four objects ("<namespace>/<name>"), chosen to test prefix
// boundaries: "ns-1" is not "ns-11", "pod-1" is not "pod-11".
func workloadKeys() []string {
	return []string{"ns-1/pod-1", "ns-1/pod-11", "ns-2/pod-2", "ns-11/pod-1"}
}

func workloadVals() []string {
	return []string{"x", "y", "z"}
}

// workloadNodes and workloadApps are the test's nodeNames and appLabels ("" for none).
func workloadNodes() []string {
	return []string{"", "node-1", "node-2"}
}

func workloadApps() []string {
	return []string{"", "app-a", "app-b"}
}

// pick returns n mod m and n / m.
func pick(n uint64, m uint64) (uint64, uint64) {
	return n % m, n / m
}

// uidOf is the UID a Create draws for the number u (its two low bytes).
func uidOf(u uint64) string {
	return string([]byte{byte(u >> 8), byte(u)})
}

// withPre sets in's preconditions from the cached object c (if any): its UID if uid, its resource
// version if rv. As the test (pickPreconditions), with no cached object there are none.
func withPre(in Input, uid bool, rv bool, c Obj, hasC bool) Input {
	if !hasC {
		return in
	}
	in.HasPreUID = uid
	if uid {
		in.PreUID = c.UID
	}
	in.HasPreRV = rv
	if rv {
		in.PreRV = rvString(c.ResourceVersion)
	}
	return in
}

// minRV is a Get's minimum resource version for the draw m (out of 100) and the offset d (1 to
// 200), as the test's resolveResourceVersion: empty (30), 0 (15), 1 (10), the cached object's
// (15), and relative to it (the test's are relative to the store's current one): current (14),
// past (14), future (2); empty when a relative one has no cached object.
func minRV(m uint64, d uint64, c Obj, hasC bool) string {
	if m < 30 {
		return ""
	}
	if m < 45 {
		return rvBytes(0)
	}
	if m < 55 {
		return rvBytes(1)
	}
	if !hasC {
		return ""
	}
	r := c.ResourceVersion
	if m < 84 {
		return rvBytes(r)
	}
	if m < 98 {
		if r <= d {
			return rvBytes(1)
		}
		return rvBytes(r - d)
	}
	return rvBytes(r + d)
}

// genList is the List client id picks for the random number n on the key key with its cached
// object c (if hasC): the test's randomRequest OpList. A scope (cluster 50, namespace 25, object
// 25), then Recursive drawn again (70) over the scope's own; a field selector (everything 25, by
// name 15, by namespace 15, by node 20, by empty node 15, combined 10) and a label selector
// (everything 60, by app 40), on the key's name and namespace and a random non-empty node and app;
// a resource version as a Get's (minRV) and, if one is set, a match ("" 50, NotOlderThan 25,
// Exact 25); a limit (0 70, 1 15, 2 15) unless the resource version is set and 0. The test drops
// an Exact list at resource version 0 and resolves RVs relative to the store's current one; the
// driver makes it a legacy list, and its RVs are relative to the cached object (minRV).
func genList(n uint64, in Input, c Obj, hasC bool) Input {
	ns, name := splitKey(in.Key)
	sc, n := pick(n, 4)
	rc, n := pick(n, 10)
	fs, n := pick(n, 100)
	ls, n := pick(n, 100)
	ni, n := pick(n, 2)
	ai, n := pick(n, 2)
	m, n := pick(n, 100)
	d, n := pick(n, 200)
	mt, n := pick(n, 4)
	li, _ := pick(n, 100)
	in.Kind = KList
	in.ListKey = ResourcePrefix + "/"
	if sc == 2 {
		in.ListKey = ResourcePrefix + "/" + ns
	} else if sc == 3 {
		in.ListKey = storeKey(in.Key)
	}
	in.Recursive = rc < 7
	in.SelNS = ns
	in.SelName = name
	in.SelNode = workloadNodes()[1+ni]
	if fs < 25 {
		in.Field = FEverything
	} else if fs < 40 {
		in.Field = FByName
	} else if fs < 55 {
		in.Field = FByNS
	} else if fs < 75 {
		in.Field = FByNode
	} else if fs < 90 {
		in.Field = FEmptyNode
	} else {
		in.Field = FCombined
	}
	if ls >= 60 {
		in.SelApp = workloadApps()[1+ai]
	}
	in.MinRV = minRV(m, d+1, c, hasC)
	zero := false
	if in.MinRV != "" {
		r, _ := parseRV(in.MinRV)
		zero = r == 0
		if mt == 2 {
			in.Match = MNotOlderThan
		} else if mt == 3 && !zero {
			in.Match = MExact
		}
	}
	if !zero {
		if li >= 85 {
			in.Limit = 2
		} else if li >= 70 {
			in.Limit = 1
		}
	}
	return in
}

// genFrom is the operation client id picks for the random number n with its cached object c (if
// hasC), with TestCorrectness's weights (out of 100): a Create (15), a Delete (20), a Get (10), a
// List (25, genList) or a GuaranteedUpdate (30) of a random key. A Create and an update draw a
// value, a node and an app. A Delete has a UID precondition, a resource-version precondition, the
// cached object and a validateDeletion rejecting a random node a quarter of the time each; an
// update a UID and a resource-version precondition a fifth of the time each, a no-op, the cached
// object and ignoreNotFound (not with a no-op) 15% each, and a tryUpdate rejecting a random node a
// quarter; a Get ignores "not found" half the time, with a minimum (minRV).
func genFrom(n uint64, id int, c Obj, hasC bool) Input {
	keys := workloadKeys()
	vals := workloadVals()
	nodes := workloadNodes()
	apps := workloadApps()
	w, n := pick(n, 100)
	ki, n := pick(n, uint64(len(keys)))
	in := Input{Key: keys[ki], Client: id}
	if w < 15 {
		vi, n := pick(n, uint64(len(vals)))
		ni, n := pick(n, uint64(len(nodes)))
		ai, n := pick(n, uint64(len(apps)))
		u, _ := pick(n, 65536)
		in.Kind = KCreate
		in.Val = vals[vi]
		in.Node = nodes[ni]
		in.App = apps[ai]
		in.UID = uidOf(u)
		return in
	}
	if w < 35 {
		pu, n := pick(n, 4)
		pr, n := pick(n, 4)
		uc, n := pick(n, 4)
		rj, n := pick(n, 4)
		ri, _ := pick(n, uint64(len(nodes)))
		in.Kind = KDelete
		in = withPre(in, pu == 0, pr == 0, c, hasC)
		if uc == 0 && hasC {
			in.UseCached = true
			in.Cached = c
		}
		if rj == 0 {
			in.HasReject = true
			in.Reject = nodes[ri]
		}
		return in
	}
	if w < 45 {
		ig, n := pick(n, 2)
		m, n := pick(n, 100)
		d, _ := pick(n, 200)
		in.Kind = KGet
		in.IgnoreNotFound = ig == 0
		in.MinRV = minRV(m, d+1, c, hasC)
		return in
	}
	if w < 70 {
		return genList(n, in, c, hasC)
	}
	vi, n := pick(n, uint64(len(vals)))
	ni, n := pick(n, uint64(len(nodes)))
	ai, n := pick(n, uint64(len(apps)))
	pu, n := pick(n, 5)
	pr, n := pick(n, 5)
	np, n := pick(n, 100)
	uc, n := pick(n, 100)
	ig, n := pick(n, 100)
	rj, n := pick(n, 4)
	ri, _ := pick(n, uint64(len(nodes)))
	in.Kind = KUpdate
	in.Val = vals[vi]
	in.Node = nodes[ni]
	in.App = apps[ai]
	// No RV precondition with a cached object (the scope premise of notes/k8s-etcd3-plan.md, 7b):
	// the store's cached no-op skips the preconditions on a key rewritten with equal bytes
	// (issues/k8s-etcd3-cached-noop-skips-preconditions.md).
	cached := uc < 15 && hasC
	in = withPre(in, pu == 0, pr == 0 && !cached, c, hasC)
	if cached {
		in.UseCached = true
		in.Cached = c
	}
	in.IgnoreNotFound = ig < 15
	in.NoOp = np < 15 && !in.IgnoreNotFound
	if rj == 0 {
		in.HasReject = true
		in.Reject = nodes[ri]
	}
	return in
}

// A cache holds each client's cached object: its last answer with a name (the test's cachedObj).
type cache struct {
	mu   sync.Mutex
	objs map[int]Obj
}

func newCache() *cache {
	return &cache{objs: make(map[int]Obj)}
}

// get returns client id's cached object, if any.
func (c *cache) get(id int) (Obj, bool) {
	c.mu.Lock()
	o, ok := c.objs[id]
	c.mu.Unlock()
	return o, ok
}

// put makes o client id's cached object.
func (c *cache) put(id int, o Obj) {
	c.mu.Lock()
	c.objs[id] = o
	c.mu.Unlock()
}

// Gen picks client id's next operation at random (genFrom of a random number and the client's
// cached object).
func Gen(tbl *cache, id int) Input {
	c, ok := tbl.get(id)
	return genFrom(primitive.RandomUint64(), id, c, ok)
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
		if se.Code == storage.ErrCodeInvalidObj {
			return Output{Err: EInvalid, ErrKey: se.Key}
		}
	}
	if storage.IsTooLargeResourceVersion(err) {
		return Output{Err: ETooLarge}
	}
	if err == errDeleteRejected || err == errUpdateRejected {
		return Output{Err: ERejected}
	}
	return Output{Err: EOther}
}

// preconditions is an input's preconditions (nil if none).
func preconditions(in Input) *storage.Preconditions {
	if !in.HasPreUID && !in.HasPreRV {
		return nil
	}
	p := &storage.Preconditions{}
	if in.HasPreUID {
		u := types.UID(in.PreUID)
		p.UID = &u
	}
	if in.HasPreRV {
		r := in.PreRV
		p.ResourceVersion = &r
	}
	return p
}

// cachedObj is an input's cached object, a new copy (nil if none).
func cachedObj(in Input) runtime.Object {
	if !in.UseCached {
		return nil
	}
	c := in.Cached
	return &c
}

// listOut is a List's output: the list it returned.
func listOut(l *ObjList) Output {
	out := Output{Err: ENone, Items: l.Items, ListRV: l.ResourceVersion, Continue: l.Continue}
	if len(out.Items) == 0 {
		out.Items = nil
	}
	if l.RemainingItemCount != nil {
		out.HasRemaining = true
		out.Remaining = *l.RemainingItemCount
	}
	return out
}

// call runs one operation through the store s: its output (the object it left in a fresh out, the
// list it left in a fresh list, or its error).
func call(s storage.Interface, in Input) Output {
	ctx := context.Background()
	if in.Kind == KList {
		l := &ObjList{}
		if err := s.GetList(ctx, in.ListKey, listOptions(in), l); err != nil {
			return errOut(err)
		}
		return listOut(l)
	}
	out := &Obj{}
	var err error
	if in.Kind == KCreate {
		ns, name := splitKey(in.Key)
		err = s.Create(ctx, storeKey(in.Key), &Obj{Namespace: ns, Name: name, UID: in.UID,
			Value: in.Val, Node: in.Node, App: in.App}, out, 0)
	} else if in.Kind == KDelete {
		err = s.Delete(ctx, storeKey(in.Key), out, preconditions(in), validateFor(in.HasReject, in.Reject),
			cachedObj(in), storage.DeleteOptions{})
	} else if in.Kind == KUpdate {
		err = s.GuaranteedUpdate(ctx, storeKey(in.Key), out, in.IgnoreNotFound, preconditions(in),
			tryUpdateFor(in), cachedObj(in))
	} else {
		err = s.Get(ctx, storeKey(in.Key),
			storage.GetOptions{IgnoreNotFound: in.IgnoreNotFound, ResourceVersion: in.MinRV}, out)
	}
	if err != nil {
		return errOut(err)
	}
	return objOut(*out)
}

// Apply runs one operation through the store s, resolving a prophecy with the output's numeric
// fields (its error kind, its error's resource version, its object's resource version): what the
// proof's linearization point compares the store's answer at a read with, the rest of the output
// following from them. An answer with a name becomes the client's cached object in tbl.
func Apply(s storage.Interface, tbl *cache, input any) any {
	in := input.(Input)
	p := primitive.NewProph()
	out := call(s, in)
	p.ResolveU64(uint64(out.Err))
	p.ResolveU64(uint64(out.ErrRV))
	p.ResolveU64(out.RV)
	if out.Err == ENone && out.Name != "" {
		tbl.put(in.Client, objOf(out))
	}
	return out
}

// Check runs lintest.Run of clients concurrent clients of the store s, each running ops
// operations, and returns porcupine's verdict against Model from the store st0 with its history
// h0.
func Check(s storage.Interface, st0 mstore, h0 []mstore, clients int, ops int, timeout time.Duration) porcupine.CheckResult {
	tbl := newCache()
	apply := func(input any) any { return Apply(s, tbl, input) }
	gen := func(id int) any { return Gen(tbl, id) }
	return lintest.Run(Model(st0, h0), apply, gen, lintest.CounterClock(), clients, ops, timeout)
}

// seedOne writes the key k's object of value "x" (no node, no app) in the older encoding directly
// through the client cli (non-canonical data, as a store with an older codec left: D30g) and
// returns the model's store st with it, or false if the put failed or did not make revision rv.
func seedOne(cli *clientv3.Client, st mstore, k string, rv uint64) (mstore, bool) {
	ns, name := splitKey(k)
	o := Obj{Namespace: ns, Name: name, Value: "x"}
	resp, err := cli.Put(context.Background(), Prefix+storeKey(k), string(encodeV0(o)))
	if err != nil || uint64(resp.Header.Revision) != rv {
		return mstore{}, false
	}
	o.ResourceVersion = rv
	return mstore{items: setItem(st.items, item{key: k, obj: o, canon: false}), rv: rv}, true
}

// seed writes the seed keys "ns-1/pod-1" and "ns-2/pod-2" in the older encoding (seedOne), at
// revisions 2 and 3 of a fresh cluster (revision 1 is its empty store), and returns the model's
// store after them with its history (the empty store, then each seed's), or false if a put failed
// or made another revision.
func seed(cli *clientv3.Client) (mstore, []mstore, bool) {
	s1 := mstore{rv: 1}
	s2, ok := seedOne(cli, s1, "ns-1/pod-1", 2)
	if !ok {
		return mstore{}, nil, false
	}
	s3, ok := seedOne(cli, s2, "ns-2/pod-2", 3)
	if !ok {
		return mstore{}, nil, false
	}
	return s3, []mstore{s1, s2, s3}, true
}

// noStreaming turns the store's EtcdRangeStream feature off (lists take the paginated path,
// pagedChunks; notes/k8s-7e-scope.md, Q7e-5), or returns false.
func noStreaming() bool {
	return utilfeature.DefaultMutableFeatureGate.Set("EtcdRangeStream=false") == nil
}

// The client address: the string net.Listen is given is the client's endpoint, verbatim (a plain
// host:port, no scheme). Not the other examples', so that their tests can run at once.
const clientAddr = "127.0.0.1:23896"

// Main starts one member of a new cluster (as examples/etcd/txnlin's Main does), connects a
// kubernetes client configured for one attempt per call, seeds the keys, makes the store and runs
// Check; it panics if porcupine finds the history illegal. An error from a step before Check ends
// Main without a check.
func Main(clients int, ops int) porcupine.CheckResult {
	lg := zap.NewNop()
	srv, err := etcdstart.StartServer("k8setcd3", "127.0.0.1:23906", clientAddr, lg)
	if err != nil {
		return porcupine.Unknown
	}
	if err := etcdstart.Serve(srv, clientAddr); err != nil {
		return porcupine.Unknown
	}

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
	st0, h0, ok := seed(kc.Client)
	if !ok || !noStreaming() {
		return porcupine.Unknown
	}
	s, err := etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix,
		schema.GroupResource{Resource: "objs"}, identity{}, etcd3.NewDefaultLeaseManagerConfig(),
		decoder{}, versioner{})
	if err != nil {
		return porcupine.Unknown
	}
	r := Check(s, st0, h0, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("k8setcd3: porcupine found the history not linearizable")
	}
	return r
}

// clusterConfig is MainCluster's three-member cluster (examples/lib/cluster3): its own token, names
// and addresses, not the other examples', so that their tests can run at once.
func clusterConfig() cluster3.Config {
	return cluster3.Config{
		Token: "k8setcd3c", Name1: "k8setcd3c-1", Name2: "k8setcd3c-2", Name3: "k8setcd3c-3",
		Peer1: "127.0.0.1:24041", Peer2: "127.0.0.1:24042", Peer3: "127.0.0.1:24043",
		Client1: "127.0.0.1:24051", Client2: "127.0.0.1:24052", Client3: "127.0.0.1:24053",
		Bridge1: "127.0.0.1:24061", Bridge2: "127.0.0.1:24062", Bridge3: "127.0.0.1:24063",
		SnapCount: 1, SnapCatchUp: 1,
	}
}

// MainCluster is Main over a three-member cluster: it starts the cluster (cluster3.StartCluster),
// connects a kubernetes client to the three members' bridges, configured as etcd's clients are in
// practice (etcdstart.NewClients' timeouts and keepalive, the default retries: a write is retried
// only after a refusal, which the members never send, so it is sent at most once), seeds the keys,
// makes the store and runs Check; it panics if porcupine finds the history illegal. An error from a
// step before Check ends MainCluster without a check.
func MainCluster(clients int, ops int) porcupine.CheckResult {
	lg := zap.NewNop()
	cfg := clusterConfig()
	_, _, ok := cluster3.StartCluster(cfg, lg)
	if !ok {
		return porcupine.Unknown
	}
	kc, err := kubernetes.New(clientv3.Config{
		Endpoints:            []string{cfg.Bridge1, cfg.Bridge2, cfg.Bridge3},
		DialTimeout:          etcdstart.DialTimeout,
		DialKeepAliveTime:    etcdstart.KeepAliveTime,
		DialKeepAliveTimeout: etcdstart.KeepAliveTimeout,
		Logger:               lg,
	})
	if err != nil {
		return porcupine.Unknown
	}
	st0, h0, ok := seed(kc.Client)
	if !ok || !noStreaming() {
		return porcupine.Unknown
	}
	s, err := etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix,
		schema.GroupResource{Resource: "objs"}, identity{}, etcd3.NewDefaultLeaseManagerConfig(),
		decoder{}, versioner{})
	if err != nil {
		return porcupine.Unknown
	}
	r := Check(s, st0, h0, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("k8setcd3: porcupine found the cluster's history not linearizable")
	}
	return r
}

// MainPartition is MainCluster under the partition schedule sched: once the store is made, the
// schedule runs (cluster3.Partitioner, on a goroutine of its own) while Check's clients run. A call
// to a member cut off from its clients ends when keepalive closes its dead transport (etcdstart's
// KeepAliveTime/KeepAliveTimeout); a write that fails is kept pending by the model (it takes
// effect later or never).
func MainPartition(clients int, ops int, sched []cluster3.Step) porcupine.CheckResult {
	lg := zap.NewNop()
	cfg := clusterConfig()
	srvs, brs, ok := cluster3.StartCluster(cfg, lg)
	if !ok {
		return porcupine.Unknown
	}
	kc, err := kubernetes.New(clientv3.Config{
		Endpoints:            []string{cfg.Bridge1, cfg.Bridge2, cfg.Bridge3},
		DialTimeout:          etcdstart.DialTimeout,
		DialKeepAliveTime:    etcdstart.KeepAliveTime,
		DialKeepAliveTimeout: etcdstart.KeepAliveTimeout,
		Logger:               lg,
	})
	if err != nil {
		return porcupine.Unknown
	}
	st0, h0, ok := seed(kc.Client)
	if !ok || !noStreaming() {
		return porcupine.Unknown
	}
	s, err := etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix,
		schema.GroupResource{Resource: "objs"}, identity{}, etcd3.NewDefaultLeaseManagerConfig(),
		decoder{}, versioner{})
	if err != nil {
		return porcupine.Unknown
	}
	go cluster3.Partitioner(srvs, brs, sched)
	r := Check(s, st0, h0, clients, ops, 0)
	if r == porcupine.Illegal {
		panic("k8setcd3: porcupine found the partitioned cluster's history not linearizable")
	}
	return r
}
