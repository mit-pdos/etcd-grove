package linkvtxn

import (
	"math"
	"math/rand"
	"testing"

	"github.com/anishathalye/porcupine"
	"go.etcd.io/etcd/tests/v3/robustness/model"
)

// The differential test (notes/linkv-txn-plan.md, stage D): random histories checked with
// Model() and with etcd's robustness model (tests/robustness/model, NonDeterministicModel, at the
// etcd fork's pin); the verdicts must agree. A history is translated as robustness's client
// records one (puts and deletes as transactions, a get or a list as a range) and with a failed
// call's return time at infinity, as robustness's validate.go sets it; Model() keeps the return
// time and lets a failed write take effect later (pending), which is the same set of histories.
// Comparisons of a value are not translated (robustness's EtcdCondition has none): the histories
// here compare versions and mod revisions only; Model()'s value comparisons are TestModel's.

func toRange(k string) model.RangeOptions { return model.RangeOptions{Start: k} }

func toOp(op TOp) model.EtcdOperation {
	switch op.Kind {
	case TGet:
		return model.EtcdOperation{Type: model.RangeOperation, Range: toRange(op.Key)}
	case TPut:
		return model.EtcdOperation{Type: model.PutOperation,
			Put: model.PutOptions{Key: op.Key, Value: model.ToValueOrHash(op.Val)}}
	default:
		return model.EtcdOperation{Type: model.DeleteOperation, Delete: model.DeleteOptions{Key: op.Key}}
	}
}

func toOps(ops []TOp) []model.EtcdOperation {
	out := []model.EtcdOperation{}
	for _, op := range ops {
		out = append(out, toOp(op))
	}
	return out
}

func toCond(c Cmp) model.EtcdCondition {
	if c.Kind == CVersion && c.Num > 0 {
		return model.EtcdCondition{Key: c.Key, ExpectedVersion: c.Num}
	}
	// a mod revision's comparison, or a version's with 0 (both: the key is missing iff 0)
	return model.EtcdCondition{Key: c.Key, ExpectedRevision: c.Num}
}

func toRequest(in Input) model.EtcdRequest {
	switch in.Kind {
	case KGet:
		return model.EtcdRequest{Type: model.Range, Range: &model.RangeRequest{RangeOptions: toRange(in.Key)}}
	case KList:
		return model.EtcdRequest{Type: model.Range,
			Range: &model.RangeRequest{RangeOptions: model.RangeOptions{Start: listFrom, End: listTo}}}
	case KPut:
		return model.EtcdRequest{Type: model.Txn, Txn: &model.TxnRequest{
			OperationsOnSuccess: toOps([]TOp{{Kind: TPut, Key: in.Key, Val: in.Val}})}}
	case KDel:
		return model.EtcdRequest{Type: model.Txn, Txn: &model.TxnRequest{
			OperationsOnSuccess: toOps([]TOp{{Kind: TDel, Key: in.Key}})}}
	default:
		conds := []model.EtcdCondition{}
		for _, c := range cmpsOf(in) {
			conds = append(conds, toCond(c))
		}
		return model.EtcdRequest{Type: model.Txn, Txn: &model.TxnRequest{Conditions: conds,
			OperationsOnSuccess: toOps(thenOf(in)), OperationsOnFailure: toOps(elseOf(in))}}
	}
}

func toKV(k string, r VR) model.KeyValue {
	return model.KeyValue{Key: k, ValueRevision: model.ValueRevision{Value: model.ToValueOrHash(r.Val),
		ModRevision: r.Mod, Version: r.Ver}}
}

func toResponse(in Input, out Output) model.MaybeEtcdResponse {
	if out.Err {
		return model.MaybeEtcdResponse{Error: "error"}
	}
	resp := model.EtcdResponse{Revision: out.Rev}
	switch in.Kind {
	case KGet:
		rr := model.RangeResponse{KVs: []model.KeyValue{}}
		if out.Found {
			rr.KVs = append(rr.KVs, toKV(in.Key, out.R))
			rr.Count = 1
		}
		resp.Range = &rr
	case KList:
		rr := model.RangeResponse{KVs: []model.KeyValue{}}
		for _, kv := range kvsOf(out) {
			rr.KVs = append(rr.KVs, toKV(kv.Key, kv.R))
		}
		rr.Count = int64(out.NKVs)
		resp.Range = &rr
	case KPut:
		resp.Txn = &model.TxnResponse{Results: []model.EtcdOperationResult{{}}}
	case KDel:
		resp.Txn = &model.TxnResponse{Results: []model.EtcdOperationResult{{Deleted: out.N}}}
	default:
		ops := elseOf(in)
		if out.Ok {
			ops = thenOf(in)
		}
		results := []model.EtcdOperationResult{}
		for i, r := range resOf(out) {
			key := ""
			if i < len(ops) {
				key = ops[i].Key
			}
			switch r.Kind {
			case TGet:
				rr := model.RangeResponse{KVs: []model.KeyValue{}}
				if r.Found {
					rr.KVs = append(rr.KVs, toKV(key, r.R))
					rr.Count = 1
				}
				results = append(results, model.EtcdOperationResult{RangeResponse: rr})
			case TPut:
				results = append(results, model.EtcdOperationResult{})
			default:
				results = append(results, model.EtcdOperationResult{Deleted: r.N})
			}
		}
		resp.Txn = &model.TxnResponse{Failure: !out.Ok, Results: results}
	}
	return model.MaybeEtcdResponse{EtcdResponse: resp}
}

// genInput is Gen without value comparisons (robustness cannot express them).
func genInput(rng *rand.Rand) Input {
	for {
		in := genFrom(rng.Uint64())
		ok := true
		for _, c := range cmpsOf(in) {
			if c.Kind == CValue {
				ok = false
			}
		}
		if ok {
			return in
		}
	}
}

// corrupt changes one field of a successful output.
func corrupt(rng *rand.Rand, in Input, out Output) Output {
	switch rng.Intn(4) {
	case 0:
		out.Rev += int64(rng.Intn(3)) - 1
	case 1:
		out.Found = !out.Found
		out.R.Ver++
	case 2:
		out.N = 1 - out.N
		out.Ok = !out.Ok
	default:
		if out.NKVs > 0 {
			out = withKVs(out, kvsOf(out)[1:])
		}
		if out.NRes > 0 && out.Res0.Kind == TGet {
			out.Res0.Found = !out.Res0.Found
		}
		out.R.Mod++
	}
	return out
}

// randomHistory runs n random operations of c clients in a random sequential order on Model()'s
// step (the true execution), lays them out as concurrent calls consistent with that order, fails
// some (a failed write taking effect at its point or not at all), and corrupts one output with
// probability 1/2.
func randomHistory(rng *rand.Rand, c, n int) ([]porcupine.Operation, []porcupine.Operation) {
	st := store{rev: 1}
	ours := []porcupine.Operation{}
	theirs := []porcupine.Operation{}
	t := int64(0)
	bad := rng.Intn(2) == 0
	badAt := rng.Intn(n)
	for i := 0; i < n; i++ {
		in := genInput(rng)
		next, out := mstep(in, st)
		if rng.Intn(6) == 0 {
			if isWrite(in) && rng.Intn(2) == 0 {
				st = next
			}
			out = Output{Err: true}
		} else {
			st = next
			if bad && i == badAt {
				out = corrupt(rng, in, out)
			}
		}
		// the call overlaps the previous one by a random amount (still in order of t)
		call := t - int64(rng.Intn(2))
		if call < 0 {
			call = 0
		}
		ret := t + 1 + int64(rng.Intn(2))
		t = ret
		client := rng.Intn(c)
		ours = append(ours, porcupine.Operation{ClientId: client, Input: in, Call: call, Output: out, Return: ret})
		r := ret
		if out.Err {
			r = math.MaxInt64
		}
		theirs = append(theirs, porcupine.Operation{ClientId: client, Input: toRequest(in), Call: call,
			Output: toResponse(in, out), Return: r})
	}
	return ours, theirs
}

func TestDifferential(t *testing.T) {
	rng := rand.New(rand.NewSource(1))
	robust := model.NonDeterministicModel(workloadKeys())
	agreeOk, agreeBad := 0, 0
	for iter := 0; iter < 20000; iter++ {
		ours, theirs := randomHistory(rng, 3, 2+rng.Intn(9))
		a := porcupine.CheckOperations(Model(), ours)
		b := porcupine.CheckOperations(robust, theirs)
		if a != b {
			t.Fatalf("iteration %d: Model() %v, robustness %v on\n%+v", iter, a, b, ours)
		}
		if a {
			agreeOk++
		} else {
			agreeBad++
		}
	}
	t.Logf("agreed on %d legal and %d illegal histories", agreeOk, agreeBad)
	if agreeBad < 100 || agreeOk < 100 {
		t.Fatalf("too few of one verdict: %d legal, %d illegal", agreeOk, agreeBad)
	}
}
