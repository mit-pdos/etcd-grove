//go:build swiftexeclog

// Test-only instrumentation, built only with the tag swiftexeclog: with
// SWIFT_EXECLOG=PREFIX, a process writes every execution, MSync and client
// reply to PREFIX.<pid> (the deployment test's stress checks read them).
package swift

import (
	"fmt"
	"os"
	"sync"

	"github.com/imdea-software/swiftpaxos/state"
)

func init() {
	prefix := os.Getenv("SWIFT_EXECLOG")
	if prefix == "" {
		return
	}
	f, err := os.Create(fmt.Sprintf("%s.%d", prefix, os.Getpid()))
	if err != nil {
		return
	}
	var mu sync.Mutex
	out := func(format string, a ...interface{}) {
		mu.Lock()
		fmt.Fprintf(f, format, a...)
		f.Sync()
		mu.Unlock()
	}
	ExecHook = func(rid int32, id CommandId, cmd state.Command, val state.Value, ballot int32) {
		out("exec %d %d %d.%d %d %d %q %q\n", rid, ballot, id.ClientId, id.SeqNum, cmd.Op, cmd.K, cmd.V, val)
	}
	SyncHook = func(rid int32, ballot int32) {
		out("sync %d %d\n", rid, ballot)
	}
	ReplyHook = func(cid int32, id CommandId, val state.Value) {
		out("reply %d %d.%d %q\n", cid, id.ClientId, id.SeqNum, val)
	}
}
