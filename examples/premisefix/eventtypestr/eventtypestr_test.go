// Package eventtypestr is the Go evidence of T5-f's mvccpb.Event_EventType.String restated over the
// pointer receiver (k8s 7f-5a-P, notes/k8s-7f5a-draft.md §11.5; the user's decision of 2026-11-15
// via etcd-grove-81: step 7 does not wait for the parked goose change emitting ptr_M_unfold for an
// axiomatized value method):
//
//	{{ isPkgInit mvccpb ∗ l ↦□ t }} (l @!! *Event_EventType @!! "String") #() {{ (s : GoString), RET #s; True }}
//
// String is a value method (kv.pb.go:50, `func (x Event_EventType) String() string`); the method
// set of *Event_EventType contains it by Go's method-set rule, as the compiler's wrapper that reads
// *l and calls the value method (the spec, "Method sets": "the method set of a pointer to a defined
// type T is the set of all methods declared with receiver *T or T"). So the pointer call reads the
// value at l (the read-only points-to), writes nothing, and returns what the value method returns,
// some string for every value (the value axiom's claim, TestEventTypeStringReturns of
// watcherctx/draft7f5a_test.go): for a nil l it panics (the spec's l ↦□ t excludes it).
//
//   - TestPtrStringIsValueString: for named, unknown and negative values, p.String() through a
//     *Event_EventType, through a fmt.Stringer holding the pointer, through a method value and
//     through the method expression (*Event_EventType).String equals t.String(), and *p is unchanged;
//     also the address of an Event's Type field, parseEvent's call shape (event.go:69, e.Type.String()
//     on a *mvccpb.Event);
//   - TestPtrStringReadsOnly (run under -race): goroutines call String through one shared pointer
//     concurrently with readers of *p: no write (the race detector would report one), the value and
//     the strings unchanged;
//   - TestPtrStringNil: a nil *Event_EventType panics (the wrapper dereferences it).
//
// Run: GOWORK=off go test -race ./premisefix/eventtypestr/ (from examples/, under a 32G cap).
package eventtypestr

import (
	"fmt"
	"sync"
	"testing"

	"go.etcd.io/etcd/api/v3/mvccpb"
)

var values = []mvccpb.Event_EventType{mvccpb.Event_PUT, mvccpb.Event_DELETE, 2, 7, -1, 1 << 30, -(1 << 31)}

func TestPtrStringIsValueString(t *testing.T) {
	for _, v := range values {
		want := v.String()
		x := v
		p := &x
		var st fmt.Stringer = p
		mv := p.String
		got := []string{p.String(), st.String(), mv(), (*mvccpb.Event_EventType).String(p)}
		for i, g := range got {
			if g != want {
				t.Errorf("value %d, form %d: %q, want %q", int32(v), i, g, want)
			}
		}
		if x != v {
			t.Errorf("value %d changed to %d", int32(v), int32(x))
		}
		e := &mvccpb.Event{Type: v}
		if s := (&e.Type).String(); s != want || e.Type != v {
			t.Errorf("field address: %q (type %d), want %q", s, int32(e.Type), want)
		}
	}
}

func TestPtrStringReadsOnly(t *testing.T) {
	for _, v := range values {
		x := v
		p := &x
		want := v.String()
		var wg sync.WaitGroup
		for g := 0; g < 8; g++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				for i := 0; i < 200; i++ {
					if g%2 == 0 {
						if s := p.String(); s != want {
							panic(fmt.Sprintf("%q != %q", s, want))
						}
					} else if *p != v {
						panic("value changed")
					}
				}
			}()
		}
		wg.Wait()
	}
}

func TestPtrStringNil(t *testing.T) {
	defer func() {
		if recover() == nil {
			t.Fatal("String through a nil *Event_EventType returned")
		}
	}()
	var p *mvccpb.Event_EventType
	_ = p.String()
}
