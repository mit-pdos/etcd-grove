package replica

import (
	"bufio"
	"bytes"
	"errors"
	"io"
	"net"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos/replica/defs"
	"github.com/imdea-software/swiftpaxos/state"
)

// errFirstReader reports an error at its first read, then serves data:
// what the lab's model of a connection allows (a reader may report an error
// and later deliver more bytes).
type errFirstReader struct {
	data   *bytes.Reader
	failed bool
}

func (e *errFirstReader) Read(p []byte) (int, error) {
	if !e.failed {
		e.failed = true
		return 0, errors.New("injected read error")
	}
	return e.data.Read(p)
}

// R-F2: clientListener peeks at the connection's first byte (P1); when the
// Peek failed it went on reading the connection as a client's. On a Peek
// error it must close the connection and return: here, the proposal served
// after the error must not reach the replica.
func TestIssueRF2_PeekErrorClosesConnection(t *testing.T) {
	r := newTestReplica(0, []string{"127.0.0.1:1", "127.0.0.1:2"})
	var buf bytes.Buffer
	buf.WriteByte(defs.PROPOSE)
	(&defs.Propose{CommandId: 1, ClientId: 7,
		Command: state.Command{Op: state.PUT, K: 1, V: state.Value("v")}}).Marshal(&buf)

	conn, other := net.Pipe()
	defer other.Close()
	done := make(chan struct{})
	go func() {
		r.clientListener(conn, bufio.NewReader(&errFirstReader{data: bytes.NewReader(buf.Bytes())}), 0, false)
		close(done)
	}()
	select {
	case <-done:
	case <-time.After(10 * time.Second):
		t.Fatal("clientListener did not return")
	}
	select {
	case p := <-r.ProposeChan:
		t.Fatalf("proposal %+v read after the failed Peek", p.Propose)
	case <-time.After(200 * time.Millisecond):
	}
	if _, err := other.Write([]byte{0}); err != io.ErrClosedPipe {
		t.Fatalf("the connection is not closed (write: %v)", err)
	}
}
