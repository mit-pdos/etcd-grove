package authmedjson

import (
	"bytes"
	"encoding/json"
	"math/rand"
	"strings"
	"testing"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
)

func randStr(r *rand.Rand) string {
	n := r.Intn(12)
	b := make([]byte, n)
	alpha := []byte{0, 0xff, 0xfe, 0xc3, 0xa9, 0xe2, 0x80, 0xa8, '<', '>', '&', '"', '\\', 'a', '\n', 0x7f}
	for i := range b {
		if r.Intn(2) == 0 {
			b[i] = alpha[r.Intn(len(alpha))]
		} else {
			b[i] = byte(r.Intn(256))
		}
	}
	return string(b)
}

func randList(r *rand.Rand) []string {
	switch r.Intn(4) {
	case 0:
		return nil
	case 1:
		return []string{}
	}
	n := r.Intn(4)
	l := make([]string, n)
	for i := range l {
		l[i] = randStr(r)
	}
	return l
}

type key struct {
	id       uint64
	ps       string
	learner  bool
	name     string
	cs       string
	psNil    bool
	promote  bool
}

func enc(l []string) string { return strings.Join(l, "\x00SEP\x00") + "#" + string(rune('0'+len(l))) }

// Output must be a function of (ID, ps, IsLearner, Name, cs) plus PeerURLs' nil-ness (the
// recommended fix); ClientURLs' nil-ness must not matter. No error ever.
func TestFunctionOfFields(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	seen := map[key]string{}
	for i := 0; i < 200000; i++ {
		m := membership.Member{ID: types.ID(r.Uint64() >> uint(r.Intn(64)))}
		m.PeerURLs = randList(r)
		m.ClientURLs = randList(r)
		m.IsLearner = r.Intn(2) == 0
		m.Name = randStr(r)
		if r.Intn(5) == 0 {
			m.Name = ""
		}
		promote := r.Intn(2) == 0
		var b []byte
		var err error
		if r.Intn(2) == 0 {
			b, err = json.Marshal(m)
			promote = false
		} else {
			b, err = json.Marshal(membership.ConfigChangeContext{Member: m, IsPromote: promote})
			b = append([]byte("C"), b...)
		}
		if err != nil {
			t.Fatalf("err %v on %#v", err, m)
		}
		k := key{uint64(m.ID), enc(m.PeerURLs), m.IsLearner, m.Name, enc(m.ClientURLs), m.PeerURLs == nil, promote}
		if b[0] == 'C' {
			k.name = "C" + k.name
		}
		if prev, ok := seen[k]; ok && prev != string(b) {
			t.Fatalf("not a function: %q vs %q", prev, b)
		}
		seen[k] = string(b)
	}
}

// Huge input: 256 MiB of NULs in Name: each becomes \u0000 (6 bytes).
func TestHuge(t *testing.T) {
	m := membership.Member{Name: string(make([]byte, 256<<20)), PeerURLs: []string{strings.Repeat("\xff", 64<<20)}}
	b, err := json.Marshal(m)
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("len %d", len(b))
	if !bytes.HasPrefix(b, []byte(`{"id":0,"peerURLs":["�`)) {
		t.Fatalf("prefix %q", b[:40])
	}
}
