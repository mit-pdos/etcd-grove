package master

import (
	"reflect"
	"testing"

	"github.com/imdea-software/swiftpaxos/config"
	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/replica/defs"
)

// A replica's register() retries after a broken rpc connection, so the same
// (addr, port) may call Register again, before and after the master is ready:
// it must keep its id and not grow nodeList.
func TestMasterReRegister(t *testing.T) {
	m := New(3, 7001, &config.Config{}, &dlog.Logger{})
	reg := func(addr string) defs.RegisterReply {
		var r defs.RegisterReply
		if err := m.Register(&defs.RegisterArgs{Addr: addr, Port: 7000}, &r); err != nil {
			t.Fatal(err)
		}
		return r
	}
	a := []string{"10.77.0.12", "10.77.0.13", "10.77.0.14"}
	if reg(a[0]).Ready || reg(a[0]).Ready || len(m.nodeList) != 1 {
		t.Fatalf("before ready: nodeList %v", m.nodeList)
	}
	reg(a[1])
	if reg(a[1]).Ready || len(m.nodeList) != 2 {
		t.Fatalf("before ready: nodeList %v", m.nodeList)
	}
	first := reg(a[2])
	want := []string{a[0] + ":7000", a[1] + ":7000", a[2] + ":7000"}
	for round := 0; round < 2; round++ {
		for i, addr := range a {
			r := reg(addr)
			if !r.Ready || r.ReplicaId != i || !reflect.DeepEqual(r.NodeList, want) {
				t.Fatalf("re-register %s: %+v", addr, r)
			}
		}
	}
	if !first.Ready || first.ReplicaId != 2 || len(m.nodeList) != 3 {
		t.Fatalf("nodeList %v, first ready reply %+v", m.nodeList, first)
	}
}
