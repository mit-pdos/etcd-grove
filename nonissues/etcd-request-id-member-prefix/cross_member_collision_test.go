// Test of nonissues/etcd-request-id-member-prefix.md: copy into pkg/idutil/ and run
// `go test ./idutil -run '^TestCrossMemberCollision$'` from pkg/. It shows only the id collision of
// two generators built as NewServer builds them (idutil.NewGenerator(uint16(memberID), time.Now())),
// not a wrong result through the server.
package idutil

import (
	"testing"
	"time"
)

// Two members whose 64-bit ids agree in their low 16 bits get the same prefix; the later
// member's ids are reached by the earlier one's counter.
func TestCrossMemberCollision(t *testing.T) {
	t0 := time.Unix(1700000000, 0)
	var idA, idB uint64 = 0x1234_0000_0000_beef, 0x9876_0000_0000_beef // two member ids
	a := NewGenerator(uint16(idA), t0)
	b := NewGenerator(uint16(idB), t0.Add(time.Millisecond))
	first := b.Next()
	for i := 0; i < 1000; i++ {
		if a.Next() == first {
			t.Errorf("member A's request %d has the id %x of member B's first request", i+1, first)
			return
		}
	}
}
