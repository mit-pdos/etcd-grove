package txnwork

import (
	"testing"

	"github.com/anishathalye/porcupine"
)

func op(client int, call, ret int64, in Input, out Output) porcupine.Operation {
	return porcupine.Operation{ClientId: client, Input: in, Call: call, Output: out, Return: ret}
}

// seq is a sequential history: each operation returns before the next is called.
func seq(ios ...any) []porcupine.Operation {
	ops := []porcupine.Operation{}
	for i := 0; i+1 < len(ios); i += 2 {
		t := int64(len(ops) * 2)
		ops = append(ops, op(0, t, t+1, ios[i].(Input), ios[i+1].(Output)))
	}
	return ops
}

func get(k string) Input     { return Input{Kind: KGet, Key: k} }
func putI(k, v string) Input { return Input{Kind: KPut, Key: k, Val: v} }
func del(k string) Input     { return Input{Kind: KDel, Key: k} }
func found(rev int64, v string, mod, ver int64) Output {
	return Output{Rev: rev, Found: true, R: VR{Val: v, Mod: mod, Ver: ver}}
}

func accepts(t *testing.T, name string, ops []porcupine.Operation) {
	t.Helper()
	if !porcupine.CheckOperations(Model(), ops) {
		t.Errorf("%s: rejected", name)
	}
}

func rejects(t *testing.T, name string, ops []porcupine.Operation) {
	t.Helper()
	if porcupine.CheckOperations(Model(), ops) {
		t.Errorf("%s: accepted", name)
	}
}

// TestModel checks the model on histories robustness's model accepts or rejects.
func TestModel(t *testing.T) {
	accepts(t, "put, get with revisions", seq(
		putI("k0", "a"), Output{Rev: 2},
		get("k0"), found(2, "a", 2, 1),
		putI("k0", "b"), Output{Rev: 3},
		get("k0"), found(3, "b", 3, 2)))
	rejects(t, "a get with the wrong version", seq(
		putI("k0", "a"), Output{Rev: 2},
		get("k0"), found(2, "a", 2, 2)))
	rejects(t, "a revision going backwards", seq(
		putI("k0", "a"), Output{Rev: 2},
		get("k1"), Output{Rev: 1}))
	accepts(t, "a delete of a missing key keeps the revision", seq(
		del("k0"), Output{Rev: 1, N: 0}))
	rejects(t, "a delete of a missing key counting one", seq(
		del("k0"), Output{Rev: 2, N: 1}))
	rejects(t, "a lost delete", seq(
		putI("k0", "a"), Output{Rev: 2},
		del("k0"), Output{Rev: 3, N: 1},
		get("k0"), found(3, "a", 2, 1)))
	accepts(t, "a deleted key's version restarts", seq(
		putI("k0", "a"), Output{Rev: 2},
		del("k0"), Output{Rev: 3, N: 1},
		putI("k0", "b"), Output{Rev: 4},
		get("k0"), found(4, "b", 4, 1)))
	cas := func(v string) Input {
		return mkTxn([]Cmp{{Kind: CValue, Key: "k0", Val: v}},
			[]TOp{{Kind: TPut, Key: "k0", Val: "z"}}, []TOp{{Kind: TGet, Key: "k0"}})
	}
	accepts(t, "a compare-and-set that matches", seq(
		putI("k0", "a"), Output{Rev: 2},
		cas("a"), withRes(Output{Rev: 3, Ok: true}, []TRes{{Kind: TPut}}),
		get("k0"), found(3, "z", 3, 2)))
	accepts(t, "a compare-and-set that does not match", seq(
		putI("k0", "a"), Output{Rev: 2},
		cas("b"), withRes(Output{Rev: 2, Ok: false}, []TRes{{Kind: TGet, Found: true, R: VR{"a", 2, 1}}})))
	rejects(t, "a transaction run in the wrong branch", seq(
		putI("k0", "a"), Output{Rev: 2},
		cas("b"), withRes(Output{Rev: 3, Ok: true}, []TRes{{Kind: TPut}})))
	multi := mkTxn(nil, []TOp{{Kind: TPut, Key: "k0", Val: "a"}, {Kind: TGet, Key: "k0"},
		{Kind: TDel, Key: "k1"}}, nil)
	accepts(t, "a transaction's get sees its own put, one revision", seq(
		multi, withRes(Output{Rev: 2, Ok: true}, []TRes{{Kind: TPut},
			{Kind: TGet, Found: true, R: VR{"a", 2, 1}}, {Kind: TDel, N: 0}})))
	rejects(t, "a transaction's get missing its own put", seq(
		multi, withRes(Output{Rev: 2, Ok: true}, []TRes{{Kind: TPut},
			{Kind: TGet, Found: false}, {Kind: TDel, N: 0}})))
	accepts(t, "a list", seq(
		putI("k1", "b"), Output{Rev: 2},
		putI("k0", "a"), Output{Rev: 3},
		Input{Kind: KList}, withKVs(Output{Rev: 3}, []KV{{"k0", VR{"a", 3, 1}}, {"k1", VR{"b", 2, 1}}})))
	// failed writes
	accepts(t, "a failed put taking effect late", []porcupine.Operation{
		op(0, 0, 1, putI("k0", "a"), Output{Err: true}),
		op(1, 2, 3, get("k0"), Output{Rev: 1}),
		op(1, 4, 5, get("k0"), found(2, "a", 2, 1)),
	})
	accepts(t, "a failed put never taking effect", []porcupine.Operation{
		op(0, 0, 1, putI("k0", "a"), Output{Err: true}),
		op(1, 2, 3, get("k0"), Output{Rev: 1}),
	})
	rejects(t, "a failed put taking effect twice", []porcupine.Operation{
		op(0, 0, 1, putI("k0", "a"), Output{Err: true}),
		op(1, 2, 3, get("k0"), found(2, "a", 2, 1)),
		op(1, 4, 5, get("k0"), found(3, "a", 3, 2)),
	})
	accepts(t, "a failed read constrains nothing", []porcupine.Operation{
		op(0, 0, 1, get("k0"), Output{Err: true}),
		op(0, 2, 3, Input{Kind: KList}, Output{Err: true}),
	})
}

// mkTxn is the transaction of at most MaxCmps comparisons, MaxThen then- and MaxElse
// else-operations (any beyond are dropped).
func mkTxn(cmps []Cmp, then []TOp, els []TOp) Input {
	in := Input{Kind: KTxn}
	if len(cmps) > 0 {
		in.NCmps = 1
		in.Cmp0 = cmps[0]
	}
	if len(then) > 0 {
		in.Then0 = then[0]
		in.NThen = 1
	}
	if len(then) > 1 {
		in.Then1 = then[1]
		in.NThen = 2
	}
	if len(then) > 2 {
		in.Then2 = then[2]
		in.NThen = 3
	}
	if len(els) > 0 {
		in.Else0 = els[0]
		in.NElse = 1
	}
	return in
}
