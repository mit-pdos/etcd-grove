package log

import (
	"fmt"
	"testing"
)

func logsOf(n int) Logs {
	l := NewLogs()
	for i := 1; i <= n; i++ {
		l.Add(Log{Data: fmt.Sprintf("op%d", i), ClientID: 1, RequestID: uint64(i)})
	}
	return l
}

// V4: TruncateAfter(i) keeps ops 1..i (ops are numbered from 1: OpAt(i) is the i-th entry), so
// that after truncating to a commit number c, OpAt(c) is still op c and the op number c matches
// the log's length.
func TestFixV4TruncateAfterKeepsOpsUpToI(t *testing.T) {
	for _, tc := range []struct{ n, i int }{{3, 2}, {3, 3}, {3, 0}, {1, 1}} {
		func() {
			defer func() {
				if p := recover(); p != nil {
					t.Errorf("V4: TruncateAfter(%d) on %d ops panicked (%v); it must keep ops 1..%d", tc.i, tc.n, p, tc.i)
				}
			}()
			l := logsOf(tc.n)
			l.TruncateAfter(tc.i)
			if l.Len() != tc.i {
				t.Errorf("V4: TruncateAfter(%d) on %d ops kept %d ops; it must keep ops 1..%d", tc.i, tc.n, l.Len(), tc.i)
				return
			}
			if tc.i > 0 && l.OpAt(tc.i) != fmt.Sprintf("op%d", tc.i) {
				t.Errorf("V4: after TruncateAfter(%d), OpAt(%d) = %q", tc.i, tc.i, l.OpAt(tc.i))
			}
		}()
	}
}
