package dist

// The store workload's wire: the driver's Input and Output (examples/k8s/etcd3, through its
// export.go) as bytes, every field in order through examples/etcd/dist/enc, and the Output's Raw
// (what the store returned, which only the maintainers' checker reads) in an encoding of the
// values the store returns: an *Obj or *ObjList, a *storage.StorageError, the callbacks' own
// errors, a *apierrors.StatusError (its Status as JSON), and watch events of those objects or of a
// *metav1.Status. The API server's machine checks that the Raw it sends decodes to a value
// reflect.DeepEqual to the store's (RawOK): Kubernetes' checker compares responses with
// reflect.DeepEqual, so a Raw that would not survive the wire is flagged, never sent altered, and
// the orchestrator then skips that checker (Store's result line says so). The API server also says
// whether the store answered etcd's "compacted" (Compacted), read off the store's own answer.

import (
	"encoding/json"
	"reflect"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/watch"
	"k8s.io/apiserver/pkg/storage"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/enc"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"

	k8s "github.com/mit-pdos/etcd-grove/examples/k8s/etcd3"
)

// StoreOut is an API server's answer: the driver's output, whether its Raw crossed the wire
// unchanged, and whether the store's answer was etcd's "compacted" (Compacted, which the API
// server reads off the store's own answer, carried or not).
type StoreOut struct {
	Out       k8s.Output
	RawOK     bool
	Compacted bool
}

// compacted says whether the store's answer raw is etcd's "compacted", as Kubernetes' etcd3
// storage reports it (errors.go, interpretListError and interpretWatchError: ResourceExpired, 410
// Gone with reason Expired): a List's error, or a watch's Error event.
func compacted(raw k8s.Raw) bool {
	if raw.Err != nil && apierrors.IsResourceExpired(raw.Err) {
		return true
	}
	for _, ev := range raw.Events {
		if ev.Type != watch.Error {
			continue
		}
		if st, ok := ev.Object.(*metav1.Status); ok && st.Reason == metav1.StatusReasonExpired {
			return true
		}
	}
	return false
}

func encObj(e *enc.Enc, o k8s.Obj) {
	e.Str(o.Namespace)
	e.Str(o.Name)
	e.Str(o.UID)
	e.Str(o.Value)
	e.Str(o.Node)
	e.Str(o.App)
	e.U64(o.ResourceVersion)
	e.Bool(o.Annotated)
}

func decObj(d *enc.Dec) k8s.Obj {
	return k8s.Obj{Namespace: d.Str(), Name: d.Str(), UID: d.Str(), Value: d.Str(), Node: d.Str(),
		App: d.Str(), ResourceVersion: d.U64(), Annotated: d.Bool()}
}

// EncInput is in's encoding.
func EncInput(in k8s.Input) []byte {
	e := &enc.Enc{}
	e.Int(in.Kind)
	e.Str(in.Key)
	e.Str(in.Val)
	e.Str(in.Node)
	e.Str(in.App)
	e.Bool(in.HasReject)
	e.Str(in.Reject)
	e.Bool(in.NoOp)
	e.Bool(in.IgnoreNotFound)
	e.Str(in.UID)
	e.Bool(in.HasPreUID)
	e.Str(in.PreUID)
	e.Bool(in.HasPreRV)
	e.Str(in.PreRV)
	e.Bool(in.UseCached)
	encObj(e, in.Cached)
	e.Str(in.MinRV)
	e.Str(in.ListKey)
	e.Bool(in.Recursive)
	e.Int(in.Match)
	e.Int(in.Field)
	e.Str(in.SelNS)
	e.Str(in.SelName)
	e.Str(in.SelNode)
	e.Str(in.SelApp)
	e.I64(in.Limit)
	e.Int(in.Client)
	e.Str(in.WKey)
	e.Int(in.SendInit)
	e.Bool(in.Bookmarks)
	e.Int(in.Behavior)
	e.Bool(in.Skip)
	return e.B
}

// DecInput inverts EncInput, or false.
func DecInput(b []byte) (k8s.Input, bool) {
	d := enc.NewDec(b)
	var in k8s.Input
	in.Kind = d.Int()
	in.Key = d.Str()
	in.Val = d.Str()
	in.Node = d.Str()
	in.App = d.Str()
	in.HasReject = d.Bool()
	in.Reject = d.Str()
	in.NoOp = d.Bool()
	in.IgnoreNotFound = d.Bool()
	in.UID = d.Str()
	in.HasPreUID = d.Bool()
	in.PreUID = d.Str()
	in.HasPreRV = d.Bool()
	in.PreRV = d.Str()
	in.UseCached = d.Bool()
	in.Cached = decObj(d)
	in.MinRV = d.Str()
	in.ListKey = d.Str()
	in.Recursive = d.Bool()
	in.Match = d.Int()
	in.Field = d.Int()
	in.SelNS = d.Str()
	in.SelName = d.Str()
	in.SelNode = d.Str()
	in.SelApp = d.Str()
	in.Limit = d.I64()
	in.Client = d.Int()
	in.WKey = d.Str()
	in.SendInit = d.Int()
	in.Bookmarks = d.Bool()
	in.Behavior = d.Int()
	in.Skip = d.Bool()
	return in, d.Done()
}

// The tags of a Raw's objects and errors. rawLost: a value the encoding does not carry.
const (
	rawNone = iota
	rawObj
	rawList
	rawStatus
	rawStorageErr
	rawDeleteRejected
	rawUpdateRejected
	rawStatusErr
	rawLost
)

// encObject appends a returned object (nil, *Obj, *ObjList, *metav1.Status); false if it is
// another.
func encObject(e *enc.Enc, o runtime.Object) bool {
	switch v := o.(type) {
	case nil:
		e.Int(rawNone)
	case *k8s.Obj:
		if v == nil {
			e.Int(rawLost)
			return false
		}
		e.Int(rawObj)
		encObj(e, *v)
	case *k8s.ObjList:
		if v == nil {
			e.Int(rawLost)
			return false
		}
		e.Int(rawList)
		e.Bool(v.Items == nil)
		e.Int(len(v.Items))
		for _, it := range v.Items {
			encObj(e, it)
		}
		e.U64(v.ResourceVersion)
		e.Str(v.Continue)
		e.Bool(v.RemainingItemCount != nil)
		if v.RemainingItemCount != nil {
			e.I64(*v.RemainingItemCount)
		}
	case *metav1.Status:
		b, err := json.Marshal(v)
		if v == nil || err != nil {
			e.Int(rawLost)
			return false
		}
		e.Int(rawStatus)
		e.Str(string(b))
	default:
		e.Int(rawLost)
		return false
	}
	return true
}

func decObject(d *enc.Dec) runtime.Object {
	switch d.Int() {
	case rawNone:
		return nil
	case rawObj:
		o := decObj(d)
		return &o
	case rawList:
		l := &k8s.ObjList{}
		isNil := d.Bool()
		n := d.Int()
		if !isNil {
			l.Items = []k8s.Obj{}
		}
		for i := 0; d.Ok && i < n; i++ {
			l.Items = append(l.Items, decObj(d))
		}
		l.ResourceVersion = d.U64()
		l.Continue = d.Str()
		if d.Bool() {
			r := d.I64()
			l.RemainingItemCount = &r
		}
		return l
	case rawStatus:
		st := &metav1.Status{}
		if json.Unmarshal([]byte(d.Str()), st) != nil {
			d.Ok = false
		}
		return st
	case rawLost:
		// not carried: RawOK is false, and the orchestrator reads no Raw
		return nil
	}
	d.Ok = false
	return nil
}

// encErr appends a returned error; false if the encoding does not carry it.
func encErr(e *enc.Enc, err error) bool {
	del, upd := k8s.Rejections()
	switch v := err.(type) {
	case nil:
		e.Int(rawNone)
		return true
	case *storage.StorageError:
		e.Int(rawStorageErr)
		e.Int(v.Code)
		e.Str(v.Key)
		e.I64(v.ResourceVersion)
		inner := v.Unwrap()
		e.Bool(inner != nil)
		if inner != nil {
			e.Str(inner.Error())
		}
		return true
	case *apierrors.StatusError:
		b, jerr := json.Marshal(v.ErrStatus)
		if jerr != nil {
			e.Int(rawLost)
			return false
		}
		e.Int(rawStatusErr)
		e.Str(string(b))
		return true
	}
	if err == del {
		e.Int(rawDeleteRejected)
		return true
	}
	if err == upd {
		e.Int(rawUpdateRejected)
		return true
	}
	e.Int(rawLost)
	return false
}

func decErr(d *enc.Dec) error {
	del, upd := k8s.Rejections()
	switch d.Int() {
	case rawNone:
		return nil
	case rawStorageErr:
		code, key, rv := d.Int(), d.Str(), d.I64()
		if d.Bool() {
			// the constructors that set an inner error make it errors.New(msg)
			se := storage.NewInvalidObjError(key, d.Str())
			se.Code, se.ResourceVersion = code, rv
			return se
		}
		return &storage.StorageError{Code: code, Key: key, ResourceVersion: rv}
	case rawStatusErr:
		var st metav1.Status
		if json.Unmarshal([]byte(d.Str()), &st) != nil {
			d.Ok = false
		}
		return &apierrors.StatusError{ErrStatus: st}
	case rawDeleteRejected:
		return del
	case rawUpdateRejected:
		return upd
	case rawLost:
		return nil
	}
	d.Ok = false
	return nil
}

// encRaw appends r; false if a value in it is not carried.
func encRaw(e *enc.Enc, r k8s.Raw) bool {
	ok := encObject(e, r.Object)
	ok = encErr(e, r.Err) && ok
	e.Bool(r.Events == nil)
	e.Int(len(r.Events))
	for _, ev := range r.Events {
		e.Str(string(ev.Type))
		ok = encObject(e, ev.Object) && ok
	}
	return ok
}

func decRaw(d *enc.Dec) k8s.Raw {
	var r k8s.Raw
	r.Object = decObject(d)
	r.Err = decErr(d)
	isNil := d.Bool()
	n := d.Int()
	if !isNil {
		r.Events = []watch.Event{}
	}
	for i := 0; d.Ok && i < n; i++ {
		t := watch.EventType(d.Str())
		r.Events = append(r.Events, watch.Event{Type: t, Object: decObject(d)})
	}
	return r
}

// encOutput is o's encoding, Raw last, then whether the Raw is carried (as given: EncStoreOut
// sets it).
func encOutput(o StoreOut) []byte {
	e := &enc.Enc{}
	out := o.Out
	e.Int(out.Err)
	e.Str(out.ErrKey)
	e.I64(out.ErrRV)
	e.Str(out.ErrMsg)
	e.Str(out.Namespace)
	e.Str(out.Name)
	e.Str(out.UID)
	e.Str(out.Value)
	e.Str(out.Node)
	e.Str(out.App)
	e.U64(out.RV)
	e.Str(out.Items)
	e.U64(out.ListRV)
	e.Str(out.Continue)
	e.Bool(out.HasRemaining)
	e.I64(out.Remaining)
	e.Str(out.WEvents)
	e.Bool(out.WFailed)
	ok := encRaw(e, out.Raw)
	e.Bool(o.RawOK && ok)
	e.Bool(o.Compacted)
	return e.B
}

// DecOutput inverts the encoding, or false.
func DecOutput(b []byte) (StoreOut, bool) {
	d := enc.NewDec(b)
	var out k8s.Output
	out.Err = d.Int()
	out.ErrKey = d.Str()
	out.ErrRV = d.I64()
	out.ErrMsg = d.Str()
	out.Namespace = d.Str()
	out.Name = d.Str()
	out.UID = d.Str()
	out.Value = d.Str()
	out.Node = d.Str()
	out.App = d.Str()
	out.RV = d.U64()
	out.Items = d.Str()
	out.ListRV = d.U64()
	out.Continue = d.Str()
	out.HasRemaining = d.Bool()
	out.Remaining = d.I64()
	out.WEvents = d.Str()
	out.WFailed = d.Bool()
	out.Raw = decRaw(d)
	rawOK := d.Bool()
	comp := d.Bool()
	return StoreOut{Out: out, RawOK: rawOK, Compacted: comp}, d.Done()
}

// EncStoreOut is out's encoding as an API server sends it: RawOK says whether its Raw decodes to
// one reflect.DeepEqual to out.Raw, Compacted whether out.Raw is etcd's "compacted".
func EncStoreOut(out k8s.Output) []byte {
	c := compacted(out.Raw)
	b := encOutput(StoreOut{Out: out, RawOK: true, Compacted: c})
	back, ok := DecOutput(b)
	if ok && back.RawOK && reflect.DeepEqual(back.Out.Raw, out.Raw) {
		return b
	}
	return encOutput(StoreOut{Out: out, RawOK: false, Compacted: c})
}

// StoreCodec is the store workload's remote.Codec: a Get, a List and a watch are reads (they
// write nothing, and may be tried again); an operation without an answer is the driver's output of
// a failed call (EOther: a write's outcome unknown, a read's constraining nothing; a failed watch).
// The orchestrator's outputs are StoreOuts.
func StoreCodec() remote.Codec {
	return remote.Codec{
		EncIn: func(in any) []byte { return EncInput(in.(k8s.Input)) },
		DecIn: func(b []byte) (any, bool) {
			in, ok := DecInput(b)
			return in, ok
		},
		EncOut: func(out any) []byte { return EncStoreOut(out.(k8s.Output)) },
		DecOut: func(b []byte) (any, bool) {
			o, ok := DecOutput(b)
			return o, ok
		},
		IsRead: func(in any) bool { return !k8s.IsWrite(in.(k8s.Input)) },
		Unknown: func(in any) any {
			if in.(k8s.Input).Kind == k8s.KWatch {
				return StoreOut{Out: k8s.Output{WFailed: true}}
			}
			return StoreOut{Out: k8s.Output{Err: k8s.EOther}}
		},
		IsUnknown: func(out any) bool {
			o := out.(StoreOut).Out
			return o.Err == k8s.EOther || o.WFailed
		},
	}
}
