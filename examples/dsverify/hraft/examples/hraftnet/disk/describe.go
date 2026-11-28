//go:build covmachine

package disk

import (
	"fmt"

	"github.com/mit-pdos/etcd-grove/examples/lib/durable"
)

// Describe is a line on what dir holds, for the deployment tests' logs (covmachine prints it
// before a restartable server starts; not in the kit's build: tag covmachine).
func Describe(dir string) string {
	out := ""
	if s, ok := durable.Read(dir + "/n0"); ok {
		out += fmt.Sprintf("marker n0=%v", []byte(s))
	} else {
		out += "no marker"
	}
	if d, err := Open(dir); err != nil {
		out += fmt.Sprintf("; raft file: %v", err)
	} else {
		first, _ := d.FirstIndex()
		last, _ := d.LastIndex()
		term, _ := d.GetUint64([]byte("CurrentTerm"))
		out += fmt.Sprintf("; log %d..%d (%d entries), term %d, written commit index %d", first, last, len(d.ents), term, d.commit)
	}
	if s, err := OpenSnaps(dir); err != nil {
		out += fmt.Sprintf("; snap file: %v", err)
	} else if s.has {
		out += fmt.Sprintf("; snapshot (%d, term %d), %d bytes", s.meta.Index, s.meta.Term, len(s.data))
	} else {
		out += "; no snapshot"
	}
	return out
}
