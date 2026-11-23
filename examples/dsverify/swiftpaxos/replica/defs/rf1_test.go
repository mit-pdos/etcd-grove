package defs

import (
	"bytes"
	"errors"
	"io"
	"testing"

	"github.com/imdea-software/swiftpaxos/state"
)

var errInjected = errors.New("injected read error")

// faultyReader serves data, but its read at offset failAt reports
// errInjected (no bytes) once and then serves the rest: what the lab's
// model of a connection's bufio.Reader allows.
type faultyReader struct {
	data   []byte
	pos    int
	failAt int
	failed bool
}

func (f *faultyReader) Read(p []byte) (int, error) {
	if !f.failed && f.pos == f.failAt {
		f.failed = true
		return 0, errInjected
	}
	if f.pos >= len(f.data) {
		return 0, io.EOF
	}
	end := len(f.data)
	if !f.failed && f.failAt >= 0 && f.failAt < end {
		end = f.failAt
	}
	n := copy(p, f.data[f.pos:end])
	f.pos += n
	return n, nil
}

type wireMsg interface {
	Marshal(io.Writer)
	Unmarshal(io.Reader) error
}

// R-F1: an Unmarshal with a nested Unmarshal (state.Command, Key, Value)
// ignored the nested one's error and went on reading the stream: on a reader
// that reports an error and then delivers more bytes, the message was
// decoded from the wrong bytes and returned nil. Every read error of the
// message's bytes must be returned.
func TestIssueRF1_NestedUnmarshalErrors(t *testing.T) {
	cmd := state.Command{Op: state.PUT, K: 7, V: state.Value("val")}
	msgs := map[string]func() (wireMsg, wireMsg){
		"Propose": func() (wireMsg, wireMsg) {
			return &Propose{CommandId: 1, ClientId: 2, Command: cmd, Timestamp: 3}, new(Propose)
		},
		"ProposeReplyTS": func() (wireMsg, wireMsg) {
			return &ProposeReplyTS{OK: 1, CommandId: 1, Value: state.Value("val"), Timestamp: 3}, new(ProposeReplyTS)
		},
		"Read": func() (wireMsg, wireMsg) { return &Read{CommandId: 1, Key: 7}, new(Read) },
		"ProposeAndRead": func() (wireMsg, wireMsg) {
			return &ProposeAndRead{CommandId: 1, Command: cmd, Key: 7}, new(ProposeAndRead)
		},
		"ReadReply": func() (wireMsg, wireMsg) {
			return &ReadReply{CommandId: 1, Value: state.Value("val")}, new(ReadReply)
		},
		"ProposeAndReadReply": func() (wireMsg, wireMsg) {
			return &ProposeAndReadReply{OK: 1, CommandId: 1, Value: state.Value("val")}, new(ProposeAndReadReply)
		},
	}
	for name, mk := range msgs {
		in, _ := mk()
		var buf bytes.Buffer
		in.Marshal(&buf)
		for failAt := 0; failAt < buf.Len(); failAt++ {
			_, out := mk()
			err := out.Unmarshal(&faultyReader{data: buf.Bytes(), failAt: failAt})
			if err != errInjected {
				t.Errorf("%s: read error at byte %d of %d: Unmarshal returned %v, want the error",
					name, failAt, buf.Len(), err)
			}
		}
		_, out := mk()
		if err := out.Unmarshal(bytes.NewReader(buf.Bytes())); err != nil {
			t.Errorf("%s: no read error: Unmarshal returned %v", name, err)
		}
	}
}
