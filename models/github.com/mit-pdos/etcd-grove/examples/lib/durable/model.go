// The main tree's Go model of durable (examples/lib/durable/durable.go): Read and Write are each one
// operation of the durable-state extension durableExt (GooseLang/Ext/Durable/Impl.lean), through the
// primitive stubs durableRead and durableWrite (their GooseLang models in
// TrustedCode/github_com/mit_pdos/etcd_grove/examples/lib/durable.lean). Until 2026-11-24 Read and
// Write themselves were trusted, with the same models. (The part WalTester/ translates the package
// with its bodies, over the Linux file extension, and proves them.)

package durable

// MODEL: Read (durable.go): the durable-state extension's Read, one atomic step that cannot fail:
// the entire contents of the file and true, or "" and false if there is none. What is trusted is that
// Go's body (mu held; tryRead retried until it is done: os.Open, Stat, ReadAt, a missing file
// fs.ErrNotExist) composes the operating system's file API into that operation; the model departs
// from Go only by being less defined where Go keeps retrying forever (a persistent I/O error), as a
// safety model need only cover the executions in which Go's returns. GooseLang/Ext/Durable/Impl.lean
// lists the other divergences from a real filesystem.
func Read(name string) (string, bool) {
	return durableRead(name)
}

// MODEL: Write (durable.go): the durable-state extension's Write, one atomic step that cannot fail,
// after which the file holds data durably. Go's body (mu held; tryWrite retried until it succeeds: a
// temporary file written, synced, renamed over the file and the directory synced) provides it with
// the operating system's file API; the temporary files a Write interrupted by a crash leaves behind
// are not in the model.
func Write(name string, data string) {
	durableWrite(name, data)
}

// durableRead is the durable-state extension's Read (a primitive stub; GooseLang: ExternalOp
// durableExt "Read"). Go: Go's own body of Read.
func durableRead(name string) (string, bool) {
	mu.Lock()
	defer mu.Unlock()
	for {
		s, ok, done := tryRead(name)
		if done {
			return s, ok
		}
	}
}

// durableWrite is the durable-state extension's Write (a primitive stub; GooseLang: ExternalOp
// durableExt "Write"). Go: Go's own body of Write.
func durableWrite(name string, data string) {
	mu.Lock()
	defer mu.Unlock()
	for !tryWrite(name, data) {
	}
}
