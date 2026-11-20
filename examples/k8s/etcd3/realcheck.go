package etcd3

// Stage 7g (notes/k8s-7g-scope.md): Kubernetes' own checker on the driver's histories. After the
// driver's own check (lintest.RunLin2 with Model) answers Ok, and when no call failed, Check runs
// TestCorrectness's pipeline (k8s.io/kubernetes test/integration/apiserver/storage/
// correctness_test.go, testCorrectness, at 878cfa6c4cc7) with the maintainers' code, the copy in
// ./correctness (upstream's k8s.io/apiserver/pkg/storage/testing/correctness at the driver's pin,
// plus etc/k8s-correctness/d30g.patch; etc/k8s-correctness-check.py): porcupine over
// correctness.Model on the unary operations, correctness.NewReplay along porcupine's
// linearization, Replay.Validate of every operation, WatchValidator.ValidateWatch of every watch.
// Upstream's checker is only defined on failure-free histories (TestCorrectness fails on any
// client error), so the driver's model keeps deciding the runs with failed calls (design A').
//
// The glue below is TestCorrectness's (ToPorcupineModel, toPorcupineOperations,
// orderByLinearization and the lines of testCorrectness that run the pipeline), with three
// departures, each in the Scope: the drawn resource versions are floored at the seeds' revision
// (D7g-1, floored); a watch's events are cut after its first Error event (D7g-2); a watch-list
// whose events end before any bookmark is validated with no events (D7g-3).

import (
	"time"

	"github.com/anishathalye/porcupine"

	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/watch"
	"k8s.io/apiserver/pkg/storage"

	"github.com/mit-pdos/etcd-grove/examples/k8s/etcd3/correctness"
)

// failureFree is whether no operation of ops failed with the client's error: no unary output
// EOther, and no watch (not skipped) whose Watch call failed. The maintainers' checker is defined
// on such histories only.
func failureFree(ops []porcupine.Operation) bool {
	for _, op := range ops {
		in := op.Input.(Input)
		out := op.Output.(Output)
		if in.Kind == KWatch {
			if !in.Skip && out.WFailed {
				return false
			}
		} else if out.Err == EOther {
			return false
		}
	}
	return true
}

// realRequest is the unary input in as the maintainers' checker's request: the call call made, at
// the same store key, with the same options, preconditions, callbacks (tryUpdateFor and
// validateFor are pure functions of the input) and cached object (a fresh copy).
func realRequest(in Input) correctness.Request {
	if in.Kind == KList {
		return correctness.Request{Op: correctness.OpList, Key: in.ListKey,
			List: correctness.ListRequest{Options: listOptions(in)}}
	}
	key := storeKey(in.Key)
	if in.Kind == KCreate {
		ns, name := splitKey(in.Key)
		return correctness.Request{Op: correctness.OpCreate, Key: key, Create: correctness.CreateRequest{
			Object: &Obj{Namespace: ns, Name: name, UID: in.UID, Value: in.Val, Node: in.Node, App: in.App}}}
	}
	if in.Kind == KDelete {
		return correctness.Request{Op: correctness.OpDelete, Key: key, Delete: correctness.DeleteRequest{
			Preconditions: preconditions(in), ValidateDeletion: validateFor(in.HasReject, in.Reject),
			CachedExistingObject: cachedObj(in)}}
	}
	if in.Kind == KUpdate {
		return correctness.Request{Op: correctness.OpUpdate, Key: key, Update: correctness.UpdateRequest{
			UpdateFunc: tryUpdateFor(in), IgnoreNotFound: in.IgnoreNotFound,
			Preconditions: preconditions(in), CachedExistingObject: cachedObj(in)}}
	}
	return correctness.Request{Op: correctness.OpGet, Key: key, Get: correctness.GetRequest{
		Options: storage.GetOptions{IgnoreNotFound: in.IgnoreNotFound, ResourceVersion: in.MinRV}}}
}

// realEvents is a watch's received events as the maintainers' validator is given them: cut after
// the first Error event (D7g-2: upstream's harness reads nothing after it, and the validator
// requires it last), and none at all for a watch-list (SendInitialEvents true) with no bookmark
// among them (D7g-3: the consumer's timer, or an Error, can cut a watch-list before its
// initial-events-end bookmark, which the validator rejects;
// nonissues/k8s-correctness-watchvalidator-cut-before-bookmark.md). The driver's own check sees
// every event.
func realEvents(in Input, evs []watch.Event) []watch.Event {
	cut := evs
	for i, ev := range evs {
		if ev.Type == watch.Error {
			cut = evs[:i+1]
			break
		}
	}
	if in.SendInit == 2 {
		for _, ev := range cut {
			if ev.Type == watch.Bookmark {
				return cut
			}
		}
		return nil
	}
	return cut
}

// keyFunc is the checker's key of an object: the store key of the driver's object (its Model
// item key).
func keyFunc(obj runtime.Object) (string, error) {
	o, ok := obj.(*Obj)
	if !ok {
		return "", errNotObj
	}
	return storeKey(o.Namespace + "/" + o.Name), nil
}

// newObjList is the Model's NewListFunc.
func newObjList() runtime.Object {
	return &ObjList{}
}

// initialModel is the maintainers' Model of the seeded store st0 (TestCorrectness's
// NewModelFromStorage of the store's initial list): its items at their store keys, its resource
// version, and (the D30g patch) the keys whose stored data is not canonical, which the store
// rewrites on a no-op update.
func initialModel(st0 mstore) *correctness.Model {
	m := correctness.NewEmptyModel(Prefix, newObj, newObjList, versioner{})
	m.ResourceVersion = st0.rv
	m.NeedsRewrite = make(map[string]bool)
	for _, it := range st0.items {
		o := it.obj
		m.Items[storeKey(it.key)] = &o
		if !it.canon {
			m.NeedsRewrite[storeKey(it.key)] = true
		}
	}
	return m
}

// toPorcupineModel is TestCorrectness's ToPorcupineModel (without the descriptions, which only
// its visualization reads).
func toPorcupineModel(s *correctness.Model) porcupine.Model {
	return porcupine.Model{
		Init: func() any {
			return s.Clone()
		},
		Step: func(state, input, output any) (bool, any) {
			ok, next, _ := state.(*correctness.Model).Step(input.(correctness.Request), output.(correctness.Response))
			return ok, next
		},
		Equal: func(state1, state2 any) bool {
			return state1.(*correctness.Model).Equal(state2.(*correctness.Model))
		},
	}
}

// orderByLinearization is TestCorrectness's.
func orderByLinearization(ops []correctness.Operation, linearization []int) []correctness.Operation {
	ordered := make([]correctness.Operation, len(linearization))
	for i, idx := range linearization {
		ordered[i] = ops[idx]
	}
	return ordered
}

// realCheck runs the maintainers' checker on the history ops (lintest.RunLin2's, failure-free)
// from the seeded store st0, as testCorrectness does: porcupine over correctness.Model on the
// unary operations (their call and return times the driver's, as toPorcupineOperations takes
// them from the operations' Start and End), with the timeout timeout (0: none); NewReplay along
// the one linearization it returns; Validate of every operation in that order; ValidateWatch of
// every watch that ran. Ok if all accept, porcupine's verdict if it is not Ok, Illegal otherwise
// (where testCorrectness's require fails).
func realCheck(st0 mstore, ops []porcupine.Operation, timeout time.Duration) porcupine.CheckResult {
	var operations []correctness.Operation
	var pOps []porcupine.Operation
	var watches []correctness.WatchOperation
	for _, op := range ops {
		in := op.Input.(Input)
		out := op.Output.(Output)
		if in.Kind == KWatch {
			if !in.Skip {
				watches = append(watches, correctness.WatchOperation{
					Request:  correctness.WatchRequest{Key: in.WKey, Options: watchOptions(in)},
					Response: correctness.WatchResponse{Events: realEvents(in, out.Raw.Events)}})
			}
			continue
		}
		cop := correctness.Operation{ClientID: op.ClientId, Request: realRequest(in),
			Response: correctness.Response{Object: out.Raw.Object, Err: out.Raw.Err}}
		operations = append(operations, cop)
		pOps = append(pOps, porcupine.Operation{ClientId: op.ClientId, Input: cop.Request, Call: op.Call,
			Output: cop.Response, Return: op.Return})
	}
	initialState := initialModel(st0)
	linearizedOps := operations
	// (an empty history has no linearization in porcupine's info: nothing to order)
	if len(pOps) > 0 {
		res, info := porcupine.CheckOperationsVerbose(toPorcupineModel(initialState), pOps, timeout)
		if res != porcupine.Ok {
			return res
		}
		linearizations := info.PartialLinearizations()
		if len(linearizations) != 1 || len(linearizations[0]) != 1 {
			return porcupine.Illegal
		}
		linearizedOps = orderByLinearization(operations, linearizations[0][0])
	}
	replay, err := correctness.NewReplay(initialState, linearizedOps)
	if err != nil {
		return porcupine.Illegal
	}
	for _, op := range linearizedOps {
		if err := replay.Validate(op.Request, op.Response); err != nil {
			return porcupine.Illegal
		}
	}
	validator := correctness.NewWatchValidator(versioner{}, replay, keyFunc)
	for _, w := range watches {
		if err := validator.ValidateWatch(w.Request, w.Response); err != nil {
			return porcupine.Illegal
		}
	}
	return porcupine.Ok
}
