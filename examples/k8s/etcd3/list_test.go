package etcd3

import (
	"k8s.io/apiserver/pkg/features"
	utilfeature "k8s.io/apiserver/pkg/util/feature"

	"testing"

	"k8s.io/apiserver/pkg/storage"
	"k8s.io/apiserver/pkg/storage/testing/correctness"
)

// listFixture is a store of two keys under ns-1, pod-1 on node-1 and pod-11 on node-2, written at
// revisions 2 and 3 (revision 1 empty), with its history.
func listFixture() mcfg {
	c := mcfg{st: mstore{rv: 1}, hist: histOf([]mstore{{rv: 1}})}
	for _, in := range []Input{
		{Kind: KCreate, Key: "ns-1/pod-1", Val: "x", Node: "node-1"},
		{Kind: KCreate, Key: "ns-1/pod-11", Val: "y", Node: "node-2"},
	} {
		c, _ = seqStep(in, c)
	}
	return c
}

// TestListLimitHasMore: a list with a selector and limit 1 whose match is followed by a key in
// scope that does not match has more (a continue token, no remaining count: the predicate is not
// empty), as etcd3's store answers (its limitReached at the next key, matching or not) and the
// real Model; with no key after the match it has none; with an empty predicate the remaining count
// is the keys in scope after the limit.
func TestListLimitHasMore(t *testing.T) {
	c := listFixture()
	byNode := Input{Kind: KList, ListKey: "/objs/", Recursive: true, Field: FByNode, SelNode: "node-1", Limit: 1}
	o := mlist(byNode, c)
	if o.Err != ENone || len(decodeItems(o.Items)) != 1 || decodeItems(o.Items)[0].Name != "pod-1" || o.Continue == "" || o.HasRemaining {
		t.Fatalf("node-1, limit 1: %+v", o)
	}
	last := byNode
	last.SelNode = "node-2"
	if o := mlist(last, c); o.Err != ENone || len(decodeItems(o.Items)) != 1 || decodeItems(o.Items)[0].Name != "pod-11" || o.Continue != "" {
		t.Fatalf("node-2, limit 1 (no key after): %+v", o)
	}
	all := Input{Kind: KList, ListKey: "/objs/", Recursive: true, Limit: 1}
	if o := mlist(all, c); o.Err != ENone || len(decodeItems(o.Items)) != 1 || o.Continue == "" || !o.HasRemaining || o.Remaining != 1 {
		t.Fatalf("everything, limit 1: %+v", o)
	}
	// the prefix boundary: ns-1 does not list ns-11, pod-1 does not list pod-11
	ns := Input{Kind: KList, ListKey: "/objs/ns-1/pod-1", Recursive: true}
	if o := mlist(ns, c); o.Err != ENone || len(decodeItems(o.Items)) != 0 {
		t.Fatalf("recursive /objs/ns-1/pod-1: %+v", o)
	}
	// the real Model gives the same answers (consistent lists: compared whole)
	real := correctness.NewEmptyModel(Prefix, newTObj, newTObjList, storage.APIObjectVersioner{})
	for _, in := range []Input{
		{Kind: KCreate, Key: "ns-1/pod-1", Val: "x", Node: "node-1"},
		{Kind: KCreate, Key: "ns-1/pod-11", Val: "y", Node: "node-2"},
	} {
		_, out := seqStep(in, mcfg{st: real2store(real), hist: nil})
		_, real, _ = real.Step(request(in), response(real, in, out))
	}
	for _, in := range []Input{byNode, last, all, ns} {
		out := mlist(in, c)
		if ok, _, _ := real.Step(request(in), response(real, in, out)); !ok {
			t.Fatalf("the real Model rejects %+v for %+v", out, in)
		}
	}
}

// real2store is the driver's store of a real Model with no items but its resource version (for
// the fixture's creates).
func real2store(m *correctness.Model) mstore {
	st := mstore{rv: m.ResourceVersion}
	for k, o := range m.Items {
		to := o.(*TObj)
		key := k[len(ResourcePrefix)+1:]
		st.items = setItem(st.items, item{key: key, canon: true, obj: Obj{Namespace: to.Namespace,
			Name: to.Name, UID: string(to.UID), Value: to.Value, Node: to.Node}})
	}
	return st
}

// TestModelRejectsStaleList: porcupine's model (Model's Step) accepts an Exact list at a past
// revision with that revision's items, and rejects it with the current store's (a stale-read
// bug: the contents of another revision), and rejects a list whose continue token has another
// start key or another resource version.
func TestModelRejectsStaleList(t *testing.T) {
	c := listFixture()
	upd := Input{Kind: KUpdate, Key: "ns-1/pod-1", Val: "z", Node: "node-1"}
	c, _ = seqStep(upd, c)
	m := Model(c.st, histList(c.hist))
	st := state{c}
	exact := Input{Kind: KList, ListKey: "/objs/ns-1", Recursive: true, MinRV: rvBytes(2), Match: MExact}
	good := mlist(exact, c)
	if ok, _ := m.Step(st, exact, good); !ok || len(decodeItems(good.Items)) != 1 || decodeItems(good.Items)[0].Value != "x" || good.ListRV != 2 {
		t.Fatalf("the model rejects the answer at revision 2: %+v", good)
	}
	latest := exact
	latest.MinRV, latest.Match = "", MLegacy
	stale := mlist(latest, c)
	stale.ListRV = 2
	if ok, _ := m.Step(st, exact, stale); ok {
		t.Fatalf("the model accepts revision 4's items at revision 2: %+v", stale)
	}
	// tokens
	lim := Input{Kind: KList, ListKey: "/objs/", Recursive: true, Limit: 1}
	ans := mlist(lim, c)
	if ans.Continue == "" {
		t.Fatalf("no continue token: %+v", ans)
	}
	badKey, _ := storage.EncodeContinue(Prefix+storeKey("ns-1/pod-11")+"\x00", Prefix+"/objs/", int64(c.st.rv))
	badRV, _ := storage.EncodeContinue(Prefix+storeKey("ns-1/pod-1")+"\x00", Prefix+"/objs/", int64(c.st.rv-1))
	for _, tok := range []string{badKey, badRV} {
		bad := ans
		bad.Continue = tok
		if ok, _ := m.Step(st, lim, bad); ok || tok == ans.Continue {
			t.Fatalf("the model accepts the token %q for %q", tok, ans.Continue)
		}
	}
	if ok, _ := m.Step(st, lim, ans); !ok {
		t.Fatalf("the model rejects the right token")
	}
}

// TestNoStreaming: the switch Main makes turns the store's EtcdRangeStream feature off (lists take
// pagedChunks).
func TestNoStreaming(t *testing.T) {
	if !utilfeature.DefaultFeatureGate.Enabled(features.EtcdRangeStream) {
		t.Fatal("EtcdRangeStream is off before the switch")
	}
	if !noStreaming() || utilfeature.DefaultFeatureGate.Enabled(features.EtcdRangeStream) {
		t.Fatal("EtcdRangeStream is still on")
	}
}

// histList is a history's stores, by revision.
func histList(h *hnode) []mstore {
	var out []mstore
	for ; h != nil; h = h.prev {
		out = append([]mstore{h.st}, out...)
	}
	return out
}

// decodeItems is encodeItems' inverse (a test helper): the items of an Output's encoding.
func decodeItems(s string) []Obj {
	var items []Obj
	b := []byte(s)
	for len(b) >= 16 {
		rv, _ := parseRV(string(b[:8]))
		n, _ := parseRV(string(b[8:16]))
		o, ok := decodeObj(b[16 : 16+n])
		if !ok {
			panic("decodeItems: bad item")
		}
		o.ResourceVersion = rv
		items = append(items, o)
		b = b[16+n:]
	}
	if len(b) != 0 {
		panic("decodeItems: trailing bytes")
	}
	return items
}

// TestEncodeItemsRoundTrip checks decodeItems(encodeItems(items)) = items.
func TestEncodeItemsRoundTrip(t *testing.T) {
	items := []Obj{{Namespace: "ns-1", Name: "pod-1", UID: "u", Value: "v", Node: "n", App: "a", ResourceVersion: 3},
		{Namespace: "ns-11", Name: "pod-1", ResourceVersion: 1 << 40}, {}}
	got := decodeItems(encodeItems(items))
	if len(got) != len(items) {
		t.Fatalf("got %d items", len(got))
	}
	for i := range items {
		if got[i] != items[i] {
			t.Fatalf("item %d: %+v != %+v", i, got[i], items[i])
		}
	}
	if encodeItems(nil) != "" || len(decodeItems("")) != 0 {
		t.Fatal("empty")
	}
}

// TestCodecDecodeNil checks the codec's Decode with no object to decode into (runtime.Decode, as
// the etcd3 watcher calls it): a new object.
func TestCodecDecodeNil(t *testing.T) {
	o := Obj{Namespace: "ns-1", Name: "pod-1", UID: "u", Value: "v", Node: "n", App: "a"}
	got, _, err := codec{}.Decode(encodeObj(&o), nil, nil)
	if err != nil || *got.(*Obj) != o {
		t.Fatalf("Decode(nil) = %v, %v", got, err)
	}
	var a Obj
	a.SetAnnotations(map[string]string{"k8s.io/initial-events-end": "true"})
	if !a.Annotated || a.GetAnnotations()["k8s.io/initial-events-end"] != "true" {
		t.Fatal("annotation")
	}
}
