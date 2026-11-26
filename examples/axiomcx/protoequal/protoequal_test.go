// Package protoequal: evidence for the review of proto.EqualStatus.wp_proof
// (notes/axiom-review/proto-equal-status.md). Go only: no Goose project, no Lean proof.
package protoequal

import (
	"errors"
	"sync"
	"testing"

	spb "google.golang.org/genproto/googleapis/rpc/status"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/known/anypb"
)

func eq(t *testing.T, name string, f func() bool) (res bool, panicked any) {
	t.Helper()
	defer func() {
		if r := recover(); r != nil {
			panicked = r
			t.Logf("%s: PANIC %v", name, r)
		}
	}()
	res = f()
	t.Logf("%s: %v", name, res)
	return
}

// The cases the spec covers that do not panic.
func TestEqualStatusNoPanic(t *testing.T) {
	eq(t, "code 0 vs code 0", func() bool { return proto.Equal(&spb.Status{}, &spb.Status{}) })
	eq(t, "code 1 vs code 2", func() bool { return proto.Equal(&spb.Status{Code: 1}, &spb.Status{Code: 2}) })
	eq(t, "msg a vs msg b", func() bool { return proto.Equal(&spb.Status{Message: "a"}, &spb.Status{Message: "b"}) })
	eq(t, "nil Any vs nil Any", func() bool {
		return proto.Equal(&spb.Status{Details: []*anypb.Any{nil}}, &spb.Status{Details: []*anypb.Any{nil}})
	})
	eq(t, "nil Any vs empty Any", func() bool {
		return proto.Equal(&spb.Status{Details: []*anypb.Any{nil}}, &spb.Status{Details: []*anypb.Any{{}}})
	})
	eq(t, "Any malformed Value", func() bool {
		return proto.Equal(&spb.Status{Details: []*anypb.Any{{TypeUrl: "x", Value: []byte{0xff}}}},
			&spb.Status{Details: []*anypb.Any{{TypeUrl: "x", Value: []byte{0xfe}}}})
	})
	// Well-formed unknown fields of equal length, different bytes (what proto.Unmarshal stores).
	wf := func(b []byte) *spb.Status {
		s := &spb.Status{Code: 5}
		if err := proto.Unmarshal(b, s); err != nil {
			t.Fatal(err)
		}
		return s
	}
	eq(t, "well-formed unknown, equal length", func() bool {
		return proto.Equal(wf([]byte{0x08, 0x05, 0x50, 0x01}), wf([]byte{0x08, 0x05, 0x58, 0x01}))
	})
	// Unmarshal refuses malformed wire data: no malformed unknown fields from the wire.
	if err := proto.Unmarshal([]byte{0x08, 0x05, 0xff}, &spb.Status{}); err == nil {
		t.Fatal("unmarshal accepted malformed data")
	}
	// Concurrent errors.Is on fresh statuses (lazy messageInfo init, MessageState stores).
	for i := 0; i < 200; i++ {
		a := status.New(codes.NotFound, "x").Err()
		b := status.New(codes.NotFound, "x").Err()
		var wg sync.WaitGroup
		for j := 0; j < 4; j++ {
			wg.Add(1)
			go func() { defer wg.Done(); _ = errors.Is(a, b) }()
		}
		wg.Wait()
	}
}

// Equal racing proto.Marshal on one *spb.Status with details (what RawStatusProto's callers do to
// the status a *status.Error holds, while another goroutine's (*Error).Is compares it): run with
// -race; Marshal's writes (sizeCache, MessageState) and Equal's accesses are atomic or disjoint.
func TestEqualVsMarshalRace(t *testing.T) {
	d, err := anypb.New(&spb.Status{Code: 2, Message: "d"})
	if err != nil {
		t.Fatal(err)
	}
	p := &spb.Status{Code: 5, Message: "m", Details: []*anypb.Any{d, nil}}
	q := &spb.Status{Code: 5, Message: "m", Details: []*anypb.Any{proto.Clone(d).(*anypb.Any), nil}}
	var wg sync.WaitGroup
	for j := 0; j < 4; j++ {
		wg.Add(2)
		go func() {
			defer wg.Done()
			for k := 0; k < 1000; k++ {
				if !proto.Equal(p, q) {
					panic("unequal")
				}
			}
		}()
		go func() {
			defer wg.Done()
			for k := 0; k < 1000; k++ {
				_, _ = proto.Marshal(p)
				_, _ = proto.Marshal(q)
			}
		}()
	}
	wg.Wait()
}

// The statement's gap: malformed unknown fields (protoreflect's SetUnknown, whose documentation
// requires syntactically valid bytes and allows a panic otherwise) of equal length make Equal
// panic, directly and through grpc's public API (status.FromProto clones them; (*Error).Is).
func TestMalformedUnknownPanics(t *testing.T) {
	bad := func(b byte) *spb.Status {
		s := &spb.Status{Code: 5, Message: "m"}
		s.ProtoReflect().SetUnknown([]byte{b})
		return s
	}
	if _, p := eq(t, "malformed unknown, proto.Equal", func() bool { return proto.Equal(bad(0xff), bad(0xfe)) }); p == nil {
		t.Fatal("no panic")
	}
	if _, p := eq(t, "malformed unknown, FromProto + errors.Is", func() bool {
		return errors.Is(status.FromProto(bad(0xff)).Err(), status.FromProto(bad(0xfe)).Err())
	}); p == nil {
		t.Fatal("no panic")
	}
	badAny := func(b byte) *spb.Status {
		a := &anypb.Any{TypeUrl: "x"}
		a.ProtoReflect().SetUnknown([]byte{b})
		return &spb.Status{Code: 5, Details: []*anypb.Any{a}}
	}
	if _, p := eq(t, "malformed Any unknown, FromProto + errors.Is", func() bool {
		return errors.Is(status.FromProto(badAny(0xff)).Err(), status.FromProto(badAny(0xfe)).Err())
	}); p == nil {
		t.Fatal("no panic")
	}
}
