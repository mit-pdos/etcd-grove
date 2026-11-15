package etcd3

import (
	"context"
	"reflect"
	"strconv"
	"testing"

	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/fields"
	"k8s.io/apimachinery/pkg/labels"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/apiserver/pkg/storage"
	"k8s.io/apiserver/pkg/storage/testing/correctness"
)

// TObj is the driver's object as a Kubernetes object (an ObjectMeta, with the app label), for the
// real Model.
type TObj struct {
	metav1.TypeMeta
	metav1.ObjectMeta
	Value string
	Node  string
}

func (o *TObj) DeepCopyObject() runtime.Object {
	c := *o
	c.ObjectMeta = *o.ObjectMeta.DeepCopy()
	return &c
}

func newTObj() runtime.Object { return &TObj{} }

// TObjList is the driver's list as a Kubernetes list, for the real Model.
type TObjList struct {
	metav1.TypeMeta
	metav1.ListMeta
	Items []TObj
}

func (l *TObjList) DeepCopyObject() runtime.Object {
	c := *l
	c.ListMeta = *l.ListMeta.DeepCopy()
	c.Items = nil
	for _, o := range l.Items {
		c.Items = append(c.Items, *o.DeepCopyObject().(*TObj))
	}
	return &c
}

func newTObjList() runtime.Object { return &TObjList{} }

// tObj is an Obj as a TObj.
func tObj(o Obj) TObj {
	return TObj{ObjectMeta: metav1.ObjectMeta{Namespace: o.Namespace, Name: o.Name, UID: types.UID(o.UID),
		ResourceVersion: decRV(o.ResourceVersion), Labels: objLabels(o)}, Value: o.Value, Node: o.Node}
}

// tGetAttrs is getAttrs on TObj.
func tGetAttrs(obj runtime.Object) (labels.Set, fields.Set, error) {
	o := obj.(*TObj)
	return labels.Set(o.Labels), fields.Set{"metadata.name": o.Name,
		"metadata.namespace": o.Namespace, "spec.nodeName": o.Node}, nil
}

// tListOptions is a List's options for the real Model (the resource version decimal, getAttrs on
// TObj).
func tListOptions(in Input) storage.ListOptions {
	opts := listOptions(in)
	opts.ResourceVersion = decStr(in.MinRV)
	opts.Predicate.GetAttrs = tGetAttrs
	return opts
}

// The test's callbacks on TObj, as the driver's on Obj.
func tValidateFor(rejects bool, reject string) storage.ValidateObjectFunc {
	return func(ctx context.Context, obj runtime.Object) error {
		o := obj.(*TObj)
		if rejects && o.Node == reject {
			return errDeleteRejected
		}
		return nil
	}
}

func tTryUpdateFor(in Input) storage.UpdateFunc {
	return func(input runtime.Object, res storage.ResponseMeta) (runtime.Object, *uint64, error) {
		o := input.(*TObj)
		if in.HasReject && o.Node == in.Reject {
			return nil, nil, errUpdateRejected
		}
		c := o.DeepCopyObject().(*TObj)
		if !in.NoOp {
			if c.Name == "" {
				c.Namespace, c.Name = splitKey(in.Key)
			}
			c.Value = in.Val
			c.Node = in.Node
			c.Labels = objLabels(Obj{App: in.App})
		}
		return c, nil, nil
	}
}

// decRV is a resource version as Kubernetes' objects keep it (decimal, empty for 0).
func decRV(rv uint64) string {
	if rv == 0 {
		return ""
	}
	return strconv.FormatUint(rv, 10)
}

// decStr is a resource version string of the driver's versioner as a decimal one ("" stays "").
func decStr(s string) string {
	if s == "" {
		return ""
	}
	n, err := parseRV(s)
	if err != nil {
		panic(err)
	}
	return strconv.FormatUint(n, 10)
}

// tPre is an input's preconditions, for the real Model (the resource version decimal).
func tPre(in Input) *storage.Preconditions {
	if !in.HasPreUID && !in.HasPreRV {
		return nil
	}
	p := &storage.Preconditions{}
	if in.HasPreUID {
		u := types.UID(in.PreUID)
		p.UID = &u
	}
	if in.HasPreRV {
		r := decStr(in.PreRV)
		p.ResourceVersion = &r
	}
	return p
}

// request is an Input as the real Model's request.
func request(in Input) correctness.Request {
	key := storeKey(in.Key)
	switch in.Kind {
	case KCreate:
		ns, name := splitKey(in.Key)
		o := tObj(Obj{Namespace: ns, Name: name, UID: in.UID, Value: in.Val, Node: in.Node, App: in.App})
		return correctness.Request{Op: correctness.OpCreate, Key: key, Create: correctness.CreateRequest{Object: &o}}
	case KDelete:
		return correctness.Request{Op: correctness.OpDelete, Key: key,
			Delete: correctness.DeleteRequest{Preconditions: tPre(in), ValidateDeletion: tValidateFor(in.HasReject, in.Reject)}}
	case KUpdate:
		return correctness.Request{Op: correctness.OpUpdate, Key: key,
			Update: correctness.UpdateRequest{IgnoreNotFound: in.IgnoreNotFound, Preconditions: tPre(in), UpdateFunc: tTryUpdateFor(in)}}
	case KList:
		return correctness.Request{Op: correctness.OpList, Key: in.ListKey,
			List: correctness.ListRequest{Options: tListOptions(in)}}
	default:
		return correctness.Request{Op: correctness.OpGet, Key: key,
			Get: correctness.GetRequest{Options: storage.GetOptions{IgnoreNotFound: in.IgnoreNotFound, ResourceVersion: decStr(in.MinRV)}}}
	}
}

// response is an Output as the real Model's response (real: the real Model's state, for a failed
// precondition's message and a too-large error's current revision).
func response(real *correctness.Model, in Input, out Output) correctness.Response {
	switch out.Err {
	case EInvalid:
		var cur runtime.Object = &TObj{}
		if o, ok := real.Items[storeKey(in.Key)]; ok {
			cur = o
		}
		return correctness.Response{Err: tPre(in).Check(out.ErrKey, cur)}
	case ETooLarge:
		req, _ := parseRV(in.MinRV)
		return correctness.Response{Err: storage.NewTooLargeResourceVersionError(req, real.ResourceVersion, 0)}
	case ENotFound:
		return correctness.Response{Err: storage.NewKeyNotFoundError(out.ErrKey, out.ErrRV)}
	case EExists:
		return correctness.Response{Err: storage.NewKeyExistsError(out.ErrKey, out.ErrRV)}
	case ERejected:
		if in.Kind == KDelete {
			return correctness.Response{Err: errDeleteRejected}
		}
		return correctness.Response{Err: errUpdateRejected}
	}
	if in.Kind == KList {
		l := &TObjList{ListMeta: metav1.ListMeta{ResourceVersion: decRV(out.ListRV), Continue: out.Continue}, Items: []TObj{}}
		if out.HasRemaining {
			n := out.Remaining
			l.RemainingItemCount = &n
		}
		for _, o := range decodeItems(out.Items) {
			l.Items = append(l.Items, tObj(o))
		}
		return correctness.Response{Object: l}
	}
	if out.Name == "" && out.Value == "" && out.RV == 0 {
		return correctness.Response{Object: &TObj{}}
	}
	o := tObj(objOf(out))
	return correctness.Response{Object: &o}
}

// TestModelMatchesCorrectnessModel runs random traffic from the empty store through the driver's
// Model and the real correctness.Model at once: on every operation the real Model accepts the
// driver's model's answer, and both reach the same state; at the end, the real Replay validates
// every List along the history (a past-revision list's contents against the real Model at its
// resource version, which the real Model's step checks by resource version only). A corrupted
// answer is rejected: a write's resource version off by one by the real Model, and a past-revision
// list with another revision's items by the real Replay. (From the empty store every item is
// canonical, where the D30g fix does not change the Model.)
func TestModelMatchesCorrectnessModel(t *testing.T) {
	past, corrupted := 0, 0
	for run := 0; run < 200; run++ {
		real := correctness.NewEmptyModel(Prefix, newTObj, newTObjList, storage.APIObjectVersioner{})
		initial := real.Clone()
		c := mcfg{st: mstore{rv: 1}, hist: histOf([]mstore{{rv: 1}})}
		tbl := newCache()
		var ops []correctness.Operation
		var pastOps []int
		for i := 0; i < 80; i++ {
			in := Gen(tbl, i%3)
			next, out := seqStep(in, c)
			if out.Err == ENone && out.Name != "" {
				tbl.put(in.Client, objOf(out))
			}
			resp := response(real, in, out)
			ok, rnext, _ := real.Step(request(in), resp)
			if !ok {
				t.Fatalf("run %d op %d %+v: the real Model rejects %+v", run, i, in, out)
			}
			ops = append(ops, correctness.Operation{Request: request(in), Response: resp})
			if in.Kind == KList && out.Err == ENone {
				req, _ := parseRV(in.MinRV)
				if pastRead(in, req) {
					pastOps = append(pastOps, len(ops)-1)
				}
			}
			// a wrong answer is rejected (the resource version off by one)
			if out.Err == ENone && out.RV != 0 && in.Kind != KGet && in.Kind != KList {
				bad := out
				bad.RV = next.st.rv + 1
				if ok, _, _ := real.Step(request(in), response(real, in, bad)); ok {
					t.Fatalf("run %d op %d: the real Model accepts a wrong answer", run, i)
				}
			}
			real = rnext
			c = next
			if histLen(c.hist) != c.st.rv {
				t.Fatalf("run %d op %d: %d stores in the history at revision %d", run, i, histLen(c.hist), c.st.rv)
			}
			if real.ResourceVersion != c.st.rv || len(real.Items) != len(c.st.items) {
				t.Fatalf("run %d op %d: states differ: %d/%d items, rv %d/%d", run, i,
					len(real.Items), len(c.st.items), real.ResourceVersion, c.st.rv)
			}
			for _, it := range c.st.items {
				ro, ok := real.Items[storeKey(it.key)].(*TObj)
				want := tObj(it.obj)
				if !ok || !reflect.DeepEqual(*ro, want) {
					t.Fatalf("run %d op %d: item %s differs: %+v vs %+v", run, i, it.key, ro, want)
				}
			}
		}
		replay, err := correctness.NewReplay(initial, ops)
		if err != nil {
			t.Fatalf("run %d: %v", run, err)
		}
		for i, op := range ops {
			if err := replay.Validate(op.Request, op.Response); err != nil {
				t.Fatalf("run %d op %d: the real Replay rejects %+v: %v", run, i, op.Request.List.Options, err)
			}
		}
		// a past-revision list answered with another revision's items is rejected by the Replay
		for _, j := range pastOps {
			past++
			op := ops[j]
			l := op.Response.Object.(*TObjList)
			rv, _ := strconv.ParseUint(l.ResourceVersion, 10, 64)
			for r := uint64(1); r <= c.st.rv; r++ {
				if r == rv {
					continue
				}
				in := pastInputOf(op)
				alt := mlist(in, mcfg{st: histAt(c.hist, r)})
				if alt.Err != ENone || sameItems(alt, l) {
					continue
				}
				bad := op.Response.Object.DeepCopyObject().(*TObjList)
				bad.Items = []TObj{}
				for _, o := range decodeItems(alt.Items) {
					bad.Items = append(bad.Items, tObj(o))
				}
				if replay.Validate(op.Request, correctness.Response{Object: bad}) == nil {
					t.Fatalf("run %d op %d: the real Replay accepts revision %d's items at %d", run, j, r, rv)
				}
				corrupted++
				break
			}
		}
	}
	t.Logf("%d past-revision lists validated by the real Replay, %d corrupted ones rejected", past, corrupted)
	if past == 0 || corrupted == 0 {
		t.Fatal("no past-revision list, or none to corrupt")
	}
}

// pastInputOf is the latest-revision List of a past-revision list operation's key, scope and
// selectors (to compute another revision's items).
func pastInputOf(op correctness.Operation) Input {
	o := op.Request.List.Options
	in := Input{Kind: KList, ListKey: op.Request.Key, Recursive: o.Recursive}
	in.Field, in.SelNS, in.SelName, in.SelNode = fieldOf(o.Predicate.Field.(fieldSel))
	if ls := o.Predicate.Label.(labelSel); !ls.all {
		in.SelApp = ls.app
	}
	return in
}

// fieldOf recovers a field selector's kind and values.
func fieldOf(s fieldSel) (int, string, string, string) {
	switch {
	case s.n == 0:
		return FEverything, "", "", ""
	case s.n == 2:
		return FCombined, s.v1, "", s.v2
	case s.f1 == "metadata.name":
		return FByName, "", s.v1, ""
	case s.f1 == "metadata.namespace":
		return FByNS, s.v1, "", ""
	case s.v1 == "":
		return FEmptyNode, "", "", ""
	default:
		return FByNode, "", "", s.v1
	}
}

// sameItems says whether a model answer's items are a list's.
func sameItems(o Output, l *TObjList) bool {
	items := decodeItems(o.Items)
	if len(items) != len(l.Items) {
		return false
	}
	for i := range items {
		if !reflect.DeepEqual(tObj(items[i]), l.Items[i]) {
			return false
		}
	}
	return true
}

// TestModelNonCanonicalDiffers: on a non-canonical item a no-op update rewrites (the store does),
// which the unfixed real Model rejects (nonissues/k8s-correctness-model-noop-rewrite.md).
func TestModelNonCanonicalDiffers(t *testing.T) {
	st := mstore{items: []item{{key: "ns-1/a", obj: Obj{Namespace: "ns-1", Name: "a", Value: "x", ResourceVersion: 2}, canon: false}}, rv: 2}
	in := Input{Kind: KUpdate, Key: "ns-1/a", NoOp: true}
	_, out := mstep(in, st)
	real := correctness.NewEmptyModel(Prefix, newTObj, nil, storage.APIObjectVersioner{})
	real.ResourceVersion = 2
	real.Items[storeKey("ns-1/a")] = &TObj{ObjectMeta: metav1.ObjectMeta{Namespace: "ns-1", Name: "a", ResourceVersion: "2"}, Value: "x"}
	if ok, _, _ := real.Step(request(in), response(real, in, out)); ok {
		t.Fatalf("the unfixed Model accepts the rewrite %+v", out)
	}
}
