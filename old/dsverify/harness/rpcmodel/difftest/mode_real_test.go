//go:build !rpcmodel

package difftest_test

import "log"

// model: the tests run against the lab's models (goroot.sh's GOROOT, tag rpcmodel).
const model = false

// quiet discards real log's output (not with io.Discard: real log then skips formatting).
func quiet() { log.SetOutput(sink{}) }

type sink struct{}

func (sink) Write(p []byte) (int, error) { return len(p), nil }
