//go:build linux

package semantics

import (
	"os"
)

// A first start has nothing open (environment assumption; the initial state).
//
// Decision: a machine's first process starts with no file of the roots open
// (no fd, no mapping, no lock, no call in flight), nothing in the journal
// beyond what is durable, and the roots' trees well formed with every file
// named; together with env_durable_at_first_start.go, the state the program
// may start in.
//
// Lean: FsInit (`st.proc = ProcState.empty`, `metaLog = []`, nothing
// committed, `RootsOk`, `TreeWf`, every file named and on disk), the
// semantics' initial local state: fs_semantics's initLocal (since
// 2026-11-22), and the restricted semantics' (Premises.lean's fsSemWithS's
// initLocal, since 2026-11-24, etcd-dist D4a: its premises restrict steps and
// crashes, never the start), which Robust assumes of every machine
// (extsInitLocal). fs_interp's initP is the same predicate, so the ghost state
// is allocated for every initial state (fs_init_compat, fs_init_compatS).
//
// Excluded: a first Read of an fd the program never opened succeeding (the
// model has no such fd: the call panics, D22's convention); a lock the
// program did not take held at its start.
//
// Why: documented and measured for the fds: a process started by exec has
// only the fds its parent did not mark close-on-exec, and Go opens every
// file close-on-exec (os.OpenFile: O_CLOEXEC; syscall.forkExec passes the
// child only its ProcAttr.Files, here stdin, stdout and stderr, none of them
// in a root's tree: the net extension's TestFreshProcessNoSocket measures the
// same for sockets). A lock or mapping is a property of an open description
// or of the process, so none survives the exec either. The trees' shape is
// assumed of the deployment (the installer made the roots).
func FreshProcess(dir string) {
	// first start: no fd of dir/f is open in this process
	f, err := os.Open(dir + "/f") // the first fd the program holds on dir/f
	if err == nil {
		f.Close()
	}
	// Linux and model: the only fds on dir/f are the ones the program opened
}
