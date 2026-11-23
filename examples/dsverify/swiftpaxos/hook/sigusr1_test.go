package hook

import (
	"syscall"
	"testing"
)

// The literal hook.go registers is syscall.SIGUSR1 (linux; verification workaround).
func TestSigusr1Literal(t *testing.T) {
	if syscall.Signal(0xa) != syscall.SIGUSR1 {
		t.Fatal("0xa is not SIGUSR1 here")
	}
}
