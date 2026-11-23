package defs

import (
	"bytes"
	"testing"

	"github.com/imdea-software/swiftpaxos-epaxos/state"
)

// TestUnmarshalCutShort marshals one message of each type of this package that holds a
// state.Command, Key or Value, and unmarshals every strict prefix of its bytes (a message cut
// short by a broken connection: the stream then ends). Unmarshal must return an error for each
// prefix (io.ReadFull semantics), never deliver the message with zero fields.
func TestUnmarshalCutShort(t *testing.T) {
	cmd := state.Command{Op: state.PUT, K: 1, V: state.Value([]byte("v12"))}
	cases := []struct {
		name string
		full func(*bytes.Buffer)
		dec  func(*bytes.Reader) error
	}{
		{"Propose",
			func(b *bytes.Buffer) { (&Propose{CommandId: 1, ClientId: 2, Command: cmd, Timestamp: 3}).Marshal(b) },
			func(r *bytes.Reader) error { return (&Propose{}).Unmarshal(r) }},
		{"ProposeReplyTS",
			func(b *bytes.Buffer) {
				(&ProposeReplyTS{OK: TRUE, CommandId: 1, Value: cmd.V, Timestamp: 3}).Marshal(b)
			},
			func(r *bytes.Reader) error { return (&ProposeReplyTS{}).Unmarshal(r) }},
		{"Read",
			func(b *bytes.Buffer) { (&Read{CommandId: 1, Key: 7}).Marshal(b) },
			func(r *bytes.Reader) error { return (&Read{}).Unmarshal(r) }},
		{"ProposeAndRead",
			func(b *bytes.Buffer) { (&ProposeAndRead{CommandId: 1, Command: cmd, Key: 7}).Marshal(b) },
			func(r *bytes.Reader) error { return (&ProposeAndRead{}).Unmarshal(r) }},
		{"ReadReply",
			func(b *bytes.Buffer) { (&ReadReply{CommandId: 1, Value: cmd.V}).Marshal(b) },
			func(r *bytes.Reader) error { return (&ReadReply{}).Unmarshal(r) }},
		{"ProposeAndReadReply",
			func(b *bytes.Buffer) { (&ProposeAndReadReply{OK: TRUE, CommandId: 1, Value: cmd.V}).Marshal(b) },
			func(r *bytes.Reader) error { return (&ProposeAndReadReply{}).Unmarshal(r) }},
	}
	for _, c := range cases {
		var b bytes.Buffer
		c.full(&b)
		full := b.Bytes()
		if err := c.dec(bytes.NewReader(full)); err != nil {
			t.Fatalf("%s: whole message: %v", c.name, err)
		}
		for n := 0; n < len(full); n++ {
			if err := c.dec(bytes.NewReader(full[:n])); err == nil {
				t.Errorf("%s: cut after %d of %d bytes: Unmarshal returned nil", c.name, n, len(full))
			}
		}
	}
}
