package swift

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
// model of a connection's bufio.Reader allows. It is a byteReader, so the
// messages read it directly.
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

func (f *faultyReader) ReadByte() (byte, error) {
	var b [1]byte
	_, err := f.Read(b[:])
	return b[0], err
}

type wireMsg interface {
	Marshal(io.Writer)
	Unmarshal(io.Reader) error
}

// R-F1: MOptAcks, MAcks and MNewLeaderAckN ignored the error of their
// elements' Unmarshal (Ack, MFastAck, state.Command, SDep) and went on
// reading the stream: on a reader that reports an error and then delivers
// more bytes, the message was decoded from the wrong bytes and could return
// nil. Every read error of the message's bytes must be returned.
func TestIssueRF1_NestedUnmarshalErrors(t *testing.T) {
	deps := []CommandId{{1, 2}, {3, 4}}
	sums := []SHash{{}}
	msgs := map[string]func() (wireMsg, wireMsg){
		"MOptAcks": func() (wireMsg, wireMsg) {
			return &MOptAcks{Replica: 1, Ballot: 2, Acks: []Ack{
				{CmdId: CommandId{5, 6}, Dep: deps, Checksum: sums, Seqnum: 7},
				{CmdId: CommandId{8, 9}, Dep: deps, Checksum: sums, Seqnum: 10},
			}}, new(MOptAcks)
		},
		"MAcks": func() (wireMsg, wireMsg) {
			return &MAcks{FastAcks: []MFastAck{
				{Replica: 1, Ballot: 2, CmdId: CommandId{5, 6}, Dep: deps, Checksum: sums, Seqnum: 7},
			}, LightSlowAcks: []MLightSlowAck{{Replica: 1, Ballot: 2, CmdId: CommandId{5, 6}}}}, new(MAcks)
		},
		"MNewLeaderAckN": func() (wireMsg, wireMsg) {
			return &MNewLeaderAckN{Replica: 1, Ballot: 2, Cballot: 1,
				CmdIds: []CommandId{{5, 6}}, Phases: []int{2},
				Cmds: []state.Command{{Op: state.PUT, K: 7, V: state.Value("val")}},
				Deps: []SDep{{Dep: deps}}}, new(MNewLeaderAckN)
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
		if err := out.Unmarshal(&faultyReader{data: buf.Bytes(), failAt: -1}); err != nil {
			t.Errorf("%s: no read error: Unmarshal returned %v", name, err)
		}
	}
}
