package epaxos

import (
	"bytes"
	"errors"
	"testing"

	fastrpc "github.com/imdea-software/swiftpaxos-epaxos/rpc"
	"github.com/imdea-software/swiftpaxos-epaxos/state"
)

// failOnceReader serves data[:cut], then fails one Read, then serves the rest.
type failOnceReader struct {
	data   []byte
	cut    int
	pos    int
	failed bool
}

func (r *failOnceReader) Read(p []byte) (int, error) {
	if r.pos == r.cut && !r.failed {
		r.failed = true
		return 0, errors.New("transient read error")
	}
	end := len(r.data)
	if r.pos < r.cut {
		end = r.cut
	}
	if r.pos >= len(r.data) {
		return 0, errors.New("EOF")
	}
	n := copy(p, r.data[r.pos:end])
	r.pos += n
	return n, nil
}

// TestUnmarshalReportsCommandError: a message whose command cannot be read must not be
// decoded as a message with a zero-valued command. Each message type with commands is
// marshaled with one PUT, and the read fails once exactly where the command starts; the
// bytes after the failure happen to parse as the rest of the message (seq, an empty deps). The
// parent's Unmarshal ignores the command's error and returns nil with a NONE command.
func TestUnmarshalReportsCommandError(t *testing.T) {
	cmd := state.Command{Op: state.PUT, K: state.Key(1), V: state.Value("x")}
	var cb bytes.Buffer
	cmd.Marshal(&cb)
	cl := cb.Len()
	msgs := []fastrpc.Serializable{
		&PrepareReply{AcceptorId: 1, Replica: 0, Instance: 0, Command: []state.Command{cmd}},
		&PreAccept{LeaderId: 0, Replica: 0, Instance: 0, Command: []state.Command{cmd}},
		&Commit{LeaderId: 0, Replica: 0, Instance: 0, Command: []state.Command{cmd}},
		&TryPreAccept{LeaderId: 0, Replica: 0, Instance: 0, Command: []state.Command{cmd}},
	}
	for _, m := range msgs {
		var b bytes.Buffer
		m.Marshal(&b)
		// the message ends with the command, seq (4 bytes) and the empty deps' length (1 byte)
		cut := b.Len() - cl - 5
		got := m.New()
		err := got.Unmarshal(&failOnceReader{data: b.Bytes(), cut: cut})
		if err == nil {
			t.Errorf("%T: Unmarshal returned no error after the command could not be read: %+v", m, got)
		}
	}
}
