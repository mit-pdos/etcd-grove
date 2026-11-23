package client

import (
	"bufio"
	"bytes"
	"io"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/replica/defs"
	fastrpc "github.com/imdea-software/swiftpaxos/rpc"
)

type c1Msg struct{ X byte }

func (m *c1Msg) Marshal(w io.Writer) { w.Write([]byte{m.X}) }

func (m *c1Msg) Unmarshal(r io.Reader) error {
	var b [1]byte
	_, err := io.ReadFull(r, b[:])
	m.X = b[0]
	return err
}

func (m *c1Msg) New() fastrpc.Serializable { return new(c1Msg) }

// C1: Connect leaves the readers of the replicas the master lists as not
// alive nil; RegisterRPCTable must read only from the connected ones (a nil
// *bufio.Reader panics the client node).
func TestIssueC1_DeadReplicaReader(t *testing.T) {
	c := NewClientLog("", "10.77.0.11", 7001, true, false, false, &dlog.Logger{})
	c.replicas = []string{"10.77.0.12:7002", "10.77.0.13:7003"}

	table := fastrpc.NewTableId(defs.RPC_TABLE)
	ch := make(chan fastrpc.Serializable, 1)
	code := table.Register(new(c1Msg), ch)

	// replica 0 not alive (nil reader), replica 1 connected
	c.readers = []*bufio.Reader{nil, bufio.NewReader(bytes.NewReader([]byte{code, 42}))}
	c.RegisterRPCTable(table)
	select {
	case m := <-ch:
		if m.(*c1Msg).X != 42 {
			t.Fatalf("got %+v", m)
		}
	case <-time.After(5 * time.Second):
		t.Fatal("no message from the connected replica")
	}
	time.Sleep(200 * time.Millisecond) // a reader of replica 0, if started, has run
}
