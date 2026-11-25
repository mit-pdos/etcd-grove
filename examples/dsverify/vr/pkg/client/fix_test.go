package client

import (
	"bytes"
	"errors"
	"io"
	"log/slog"
	"testing"

	"github.com/tangledbytes/go-vsr/pkg/events"
	"github.com/tangledbytes/go-vsr/pkg/ipv4port"
	vsrtime "github.com/tangledbytes/go-vsr/pkg/time"
)

var members = []string{"127.0.0.1:7001", "127.0.0.1:7002", "127.0.0.1:7003"}

// fakeNet records the events sent; Send fails while down is set.
type fakeNet struct {
	down bool
	sent []sentEvent
}

type sentEvent struct {
	to string
	ev events.Event
}

func (n *fakeNet) Send(to ipv4port.IPv4Port, f func(io.Writer) error) error {
	if n.down {
		return errors.New("dial: connection refused")
	}
	var buf bytes.Buffer
	if err := f(&buf); err != nil {
		return err
	}
	var ev events.Event
	if err := ev.FromReader(&buf); err != nil {
		return err
	}
	n.sent = append(n.sent, sentEvent{to.String(), ev})
	return nil
}

func (n *fakeNet) Recv() (events.NetworkEvent, bool) { return events.NetworkEvent{}, false }

const timeout = 100

func newClient(t *testing.T, id uint64) (*Client, *fakeNet, *vsrtime.Virtual) {
	n := &fakeNet{}
	clock := vsrtime.NewVirtual(1)
	c, err := New(Config{ID: id, Members: members, Network: n, Time: clock, RequestTimeout: timeout,
		Logger: slog.New(slog.DiscardHandler)})
	if err != nil {
		t.Fatal(err)
	}
	return c, n, clock
}

func reply(r events.Reply) events.NetworkEvent {
	return events.NetworkEvent{Event: &events.Event{Type: events.EventReply, Data: r}}
}

// C1: a request whose first send failed is pending (Request returned false); the client must
// retry it at its timeout (Run's broadcast), not fail on a missing timer.
func TestFixC1FailedFirstSendIsRetried(t *testing.T) {
	c, n, clock := newClient(t, 1)
	n.down = true
	if c.Request("SET k v") {
		t.Fatal("Request succeeded with the network down")
	}
	n.down = false
	defer func() {
		if p := recover(); p != nil {
			t.Fatalf("C1: Run panicked with a request pending after a failed first send (%v): the pending request has no timer", p)
		}
	}()
	c.Run()
	clock.TickBy(timeout)
	c.Run()
	if len(n.sent) != len(members) {
		t.Fatalf("C1: after the timeout the pending request was sent %d times, want a broadcast to the %d replicas", len(n.sent), len(members))
	}
	for _, s := range n.sent {
		if req := s.ev.Data.(events.Request); req.ID != 1 || req.ClientID != 1 || req.Op != "SET k v" {
			t.Fatalf("C1: broadcast %+v, want the pending request", req)
		}
	}
}

// C2: a reply answers the request s of client c (VR §4.1, <REPLY v, s, x>; request numbers are
// per client): a reply with this client's pending request number but another client's id is
// not this request's result.
func TestFixC2ReplyOfAnotherClientIsNotTaken(t *testing.T) {
	c, _, _ := newClient(t, 1)
	if !c.Request("GET k0") {
		t.Fatal("Request failed")
	}
	c.Submit(reply(events.Reply{ID: 1, ClientID: 2, ViewNum: 0, Result: "v2"}))
	c.Run()
	if r, ok := c.CheckResult(); ok {
		t.Fatalf("C2: client 1 took %+v, client 2's reply, as the result of its request 1", r)
	}
	c.Submit(reply(events.Reply{ID: 1, ClientID: 1, ViewNum: 0, Result: "v1"}))
	c.Run()
	if r, ok := c.CheckResult(); !ok || r.ClientID != 1 || r.ID != 1 || r.Result != "v1" {
		t.Fatalf("C2: client 1's own reply not taken: %+v, %v", r, ok)
	}
}

// O1: the primary of view v is replica v mod n (VR §4); a client that learned a view number
// >= 2^63 from a reply must still address a replica.
func TestFixO1ClientViewNumberHighBit(t *testing.T) {
	c, n, _ := newClient(t, 1)
	if !c.Request("SET k v") {
		t.Fatal("Request failed")
	}
	const v = uint64(1)<<63 + 1
	c.Submit(reply(events.Reply{ID: 1, ClientID: 1, ViewNum: v, Result: "v"}))
	c.Run()
	if _, ok := c.CheckResult(); !ok {
		t.Fatal("reply not taken")
	}
	defer func() {
		if p := recover(); p != nil {
			t.Fatalf("O1: Request after learning view %d panicked (%v): the primary must be view mod %d", v, p, len(members))
		}
	}()
	n.sent = nil
	c.Request("GET k")
	want := members[v%uint64(len(members))]
	if len(n.sent) != 1 || n.sent[0].to != want {
		t.Fatalf("O1: request sent to %v, want the primary of view %d, %s", n.sent, v, want)
	}
}
