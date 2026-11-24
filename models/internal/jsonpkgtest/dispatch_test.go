package jsonpkgtest

import (
	"bytes"
	"encoding/json"
	"reflect"
	"testing"
)

// The encoding/json model's per-type dispatch (models/encoding/json/model.go): the same literals in
// the real build and in the model's (run.sh in internal/jsonstreamtest runs this package in both),
// with no codec registered: the roots go by their own methods.

func TestDispatchMarshal(t *testing.T) {
	rec := Rec{ID: 1, Attrs: Attrs{URLs: []string{"a", "b"}}, Name: "n", hidden: 7}
	cases := []struct {
		v    any
		want string
	}{
		{rec, `{"id":1,"urls":["a","b"],"name":"n"}`},
		{&rec, `{"id":1,"urls":["a","b"],"name":"n"}`},
		{(*Rec)(nil), `null`},
		{Ctx{Rec: Rec{ID: 2, Attrs: Attrs{Learner: true}, Next: &Attrs{}}, Promote: true},
			`{"id":2,"isLearner":true,"name":"","next":{},"isPromote":true}`},
		{&Ctx{}, `{"id":0,"name":"","isPromote":false}`},
		{(*Ctx)(nil), `null`},
		{NewToken("v1", 3), `{"v":"v1","rv":3}`},
		{TokenPtr(), `{"v":"","rv":0}`},
	}
	for _, c := range cases {
		got, err := json.Marshal(c.v)
		if err != nil || string(got) != c.want {
			t.Fatalf("Marshal(%#v) = %s, %v; want %s", c.v, got, err, c.want)
		}
		var buf bytes.Buffer
		if err := json.NewEncoder(&buf).Encode(c.v); err != nil || buf.String() != c.want+"\n" {
			t.Fatalf("Encode(%#v) = %q, %v; want %q", c.v, buf.String(), err, c.want+"\n")
		}
	}
}

func TestDispatchUnmarshal(t *testing.T) {
	var r Rec
	if err := json.Unmarshal([]byte(` {"ID":5,"urls":["x"],"name":"m","next":{"isLearner":true}} `), &r); err != nil {
		t.Fatal(err)
	}
	if want := (Rec{ID: 5, Attrs: Attrs{URLs: []string{"x"}}, Name: "m", Next: &Attrs{Learner: true}}); !reflect.DeepEqual(r, want) {
		t.Fatalf("Unmarshal into *Rec: %#v", r)
	}
	var c Ctx
	if err := json.Unmarshal([]byte(`{"id":9,"isPromote":true}`), &c); err != nil || c.ID != 9 || !c.Promote {
		t.Fatalf("Unmarshal into *Ctx: %#v, %v", c, err)
	}
	p := TokenPtr()
	if err := json.Unmarshal([]byte(`{"v":"z","rv":-4}`), p); err != nil || !reflect.DeepEqual(p, &token{"z", -4}) {
		t.Fatalf("Unmarshal into *token: %#v, %v", p, err)
	}
	// invalid JSON: an error, nothing decoded
	r2 := r
	if err := json.Unmarshal([]byte(`{"id":1`), &r2); err == nil || !reflect.DeepEqual(r2, r) {
		t.Fatalf("Unmarshal of invalid JSON: %v, %#v", err, r2)
	}
	// a nil pointer: an error
	if err := json.Unmarshal([]byte(`{}`), (*Rec)(nil)); err == nil {
		t.Fatal("Unmarshal into a nil *Rec: no error")
	}
	// a wrong kind: an error, decoding goes on
	var r3 Rec
	if err := json.Unmarshal([]byte(`{"id":"x","name":"q"}`), &r3); err == nil || r3.Name != "q" {
		t.Fatalf("Unmarshal of a wrong kind: %v, %#v", err, r3)
	}
}

// Wrap has Rec's methods by promotion: real encoding/json encodes it by its own structure; the model
// reaches Rec's methods, which are not modelled there (a panic whose value has a NotModelled method).
func TestDispatchPromoted(t *testing.T) {
	w := Wrap{Rec: Rec{ID: 3}, Extra: 4}
	var got []byte
	var p any
	func() {
		defer func() { p = recover() }()
		got, _ = json.Marshal(w)
	}()
	if !modelBuild {
		if p != nil || string(got) != `{"id":3,"name":"","extra":4}` {
			t.Fatalf("real Marshal(Wrap) = %s, %v", got, p)
		}
		return
	}
	if _, ok := p.(interface{ NotModelled() }); !ok {
		t.Fatalf("model Marshal(Wrap): %s, panic %v (want not modelled)", got, p)
	}
}
