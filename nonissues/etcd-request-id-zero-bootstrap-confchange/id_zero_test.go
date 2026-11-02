// Test of nonissues/etcd-request-id-zero-bootstrap-confchange.md: copy into pkg/idutil/ and run
// `go test ./idutil -run '^TestIDZero$'` from pkg/. It shows only that a generator can issue the id
// 0, the id of raft's bootstrap conf changes, not a wrong result through the server.
package idutil

import (
	"testing"
	"time"
)

// A member whose id has 0 low 16 bits, started at a millisecond whose low 40 bits are all
// ones, issues the request id 0 as its 256th id.
func TestIDZero(t *testing.T) {
	ms := int64(2<<40 - 1) // 2039-09-07: unixMilli mod 2^40 = 2^40 - 1
	g := NewGenerator(0, time.UnixMilli(ms))
	for i := 1; i <= 256; i++ {
		if id := g.Next(); id == 0 {
			t.Errorf("request %d has the id 0", i)
			return
		}
	}
}
