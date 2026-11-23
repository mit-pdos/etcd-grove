package swift

import (
	"bufio"
	"errors"
	"testing"
)

type brokenConn struct{ n int }

func (w *brokenConn) Write(p []byte) (int, error) {
	w.n++
	return 0, errors.New("broken connection")
}

// R7: MSync.Marshal on a broken connection must return (the error is ignored,
// as by every other Marshal), not exit the replica (log.Fatal).
func TestIssueR7_MSyncMarshalWriteError(t *testing.T) {
	m := &MSync{Replica: 1, Ballot: 4}
	w := &brokenConn{}
	m.Marshal(w)
	// as SendMsg does: through a bufio.Writer whose error is sticky
	bw := bufio.NewWriterSize(&brokenConn{}, 16)
	bw.Write(make([]byte, 32)) // fails: the error sticks
	m.Marshal(bw)
	if w.n == 0 {
		t.Fatal("Marshal wrote nothing")
	}
}
