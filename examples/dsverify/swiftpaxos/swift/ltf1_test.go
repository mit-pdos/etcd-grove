package swift

import (
	"bytes"
	"runtime"
	"sync"
	"testing"

	"github.com/imdea-software/swiftpaxos/replica"
)

// yieldingQuorum is a quorum whose Size yields the processor: MsgSet.Add
// calls Size after it has (or has not) released a rejected message, a point
// where the runtime may preempt the client's goroutine anyway.
type yieldingQuorum struct{ replica.QuorumI }

func (q yieldingQuorum) Size() int {
	runtime.Gosched()
	return q.QuorumI.Size()
}

// LT-F1: with the fast-ack pool on (useFastAckPool) in the client's process,
// a released ack must not be read again. The client's message sets released
// an ack they rejected (a light slow ack against the leader's reply always
// fails the checksum test), and handleLightSlowAck (and the MOptAcks arm)
// then read it (f.CmdId, copyFastAck(f)), while the client's own reader
// goroutines take pooled acks (client/client.go: p.Obj.New(), Unmarshal) and
// write them.
//
// One processor; a goroutine does what a reader does (take an ack from the
// pool, unmarshal command 99.0 into it, release it) whenever the client
// yields, here in its fast quorum's Size. Without -race, a read of a released
// ack shows up as a message set of command 99.0; under -race the detector
// also reports the reader's write against the client's read.
func TestIssueLTF1_ClientReadsNoReleasedAck(t *testing.T) {
	useFastAckPool = true
	defer func() { useFastAckPool = false }()
	defer runtime.GOMAXPROCS(runtime.GOMAXPROCS(1))

	c := newTestClient(5)
	c.FQ = yieldingQuorum{c.FQ}
	var buf bytes.Buffer
	(&MFastAck{Replica: 2, Ballot: 0, CmdId: cid(99, 0), Checksum: []SHash{{}}}).Marshal(&buf)
	wire := buf.Bytes()

	stop := make(chan struct{})
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for {
			select {
			case <-stop:
				return
			default:
			}
			o := (&MFastAck{}).New().(*MFastAck)
			if err := o.Unmarshal(bytes.NewReader(wire)); err != nil {
				panic(err)
			}
			releaseFastAck(o)
			runtime.Gosched()
		}
	}()

	overwritten := false
	// several commands: under -race, sync.Pool drops a quarter of the releases
	for i := int32(0); i < 64 && !overwritten; i++ {
		x := cid(1, i)
		// ballot 0's leader (replica 0) replies; replica 1's light slow ack
		// is rejected by the fast set (nil checksum)
		c.handleReply(&MReply{Replica: 0, Ballot: 0, CmdId: x, Checksum: []SHash{{}}})
		c.handleLightSlowAck(&MLightSlowAck{Replica: 1, Ballot: 0, CmdId: x})
		_, overwritten = c.slowPathH[cid(99, 0)]
	}
	close(stop)
	wg.Wait()

	if overwritten {
		t.Fatalf("the client read a released ack that a reader had overwritten (a message set of command 99.0)")
	}
}
