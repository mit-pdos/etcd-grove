package events_test

import (
	"bytes"
	"encoding/json"
	"fmt"
	"reflect"
	"testing"

	_ "github.com/tangledbytes/go-vsr/examples/vsrwire"
	"github.com/tangledbytes/go-vsr/pkg/events"
)

// The hook (decoding into Frame) and the released path (an unnamed struct) decode the same
// events from the same stream, and reject the same malformed frames with errors of the same
// types (a type error's text names the struct and field type: Frame.@type of type uint8, not
// .@type of type events.EventType; every caller only logs it).
func TestFrameDecoderAsReleased(t *testing.T) {
	var buf bytes.Buffer
	for _, ev := range []events.Event{
		{Type: events.EventRequest, Data: events.Request{ID: 1, ClientID: 2, Op: "SET k v"}},
		{Type: events.EventPrepareOK, Data: events.PrepareOK{ViewNum: 3, OpNum: 4, ReplicaID: 1}},
		{Type: events.EventReply, Data: events.Reply{ID: 1, ClientID: 2, ViewNum: 3, Result: "v"}},
	} {
		if err := ev.ToWriter(&buf); err != nil {
			t.Fatal(err)
		}
	}
	buf.WriteString(`{"@type": 300, "data": {}}` + "\n" + `{"@type": 99, "data": {}}` + "\n" + `{"@type":`)
	decodeAll := func() []string {
		dec := json.NewDecoder(bytes.NewReader(buf.Bytes()))
		var out []string
		for i := 0; i < 8; i++ {
			ev := events.Event{}
			err := ev.FromDecoder(dec)
			out = append(out, fmt.Sprintf("%T ", err)+jsonOf(ev))
		}
		return out
	}
	hooked := decodeAll()
	saved := events.SwapFrameDecoderForTest(nil)
	if saved == nil {
		t.Fatal("vsrwire's init did not install the frame decoder")
	}
	released := decodeAll()
	events.SwapFrameDecoderForTest(saved)
	if !reflect.DeepEqual(hooked, released) {
		t.Fatalf("hook:\n%q\nreleased:\n%q", hooked, released)
	}
}

func jsonOf(ev events.Event) string {
	b, _ := json.Marshal(ev)
	return string(b)
}
