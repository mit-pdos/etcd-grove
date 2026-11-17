package incomingofattack

import (
	"context"
	"testing"
	"unsafe"

	"google.golang.org/grpc/metadata"
)

type afCtx2 struct {
	context.Context
	done chan struct{}
}

func (a afCtx2) Done() <-chan struct{}                 { return a.done }
func (a afCtx2) AfterFunc(f func()) func() bool         { return func() bool { return true } }

func TestAfterFuncerRewrite(t *testing.T) {
	p := afCtx2{metadata.NewIncomingContext(context.Background(), metadata.Pairs("token", "E")), make(chan struct{})}
	c, cancel := context.WithCancel(p)
	defer cancel()
	field0 := *(*context.Context)((*iface)(unsafe.Pointer(&c)).data)
	t.Logf("field0 after WithCancel: %T; child tok=%s", field0, tok(c))
	if tok(c) != "E" {
		t.Fatal("lost")
	}
}
