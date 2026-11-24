package client

import (
	"fmt"
	"net"
	"net/http"
	"net/rpc"
	"runtime"
	"syscall"
	"testing"
	"unsafe"

	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/replica/defs"
)

type fakeMaster struct{ replicas []string }

func (m *fakeMaster) GetReplicaList(_ *defs.GetReplicaListArgs, reply *defs.GetReplicaListReply) error {
	reply.Ready = true
	reply.ReplicaList = m.replicas
	reply.AliveList = make([]bool, len(m.replicas))
	for i := range reply.AliveList {
		reply.AliveList[i] = true
	}
	return nil
}

func (m *fakeMaster) GetLeader(_ *defs.GetLeaderArgs, reply *defs.GetLeaderReply) error {
	reply.LeaderId = 0
	return nil
}

// loUp brings the loopback interface of the calling thread's namespace up.
func loUp() error {
	fd, err := syscall.Socket(syscall.AF_INET, syscall.SOCK_DGRAM, 0)
	if err != nil {
		return err
	}
	defer syscall.Close(fd)
	var ifr struct {
		name  [syscall.IFNAMSIZ]byte
		flags uint16
		_     [22]byte
	}
	copy(ifr.name[:], "lo")
	ifr.flags = syscall.IFF_UP | syscall.IFF_RUNNING
	if _, _, e := syscall.Syscall(syscall.SYS_IOCTL, uintptr(fd), syscall.SIOCSIFFLAGS,
		uintptr(unsafe.Pointer(&ifr))); e != 0 {
		return e
	}
	return nil
}

// U1: with no latency file (LatencyConf ""), Connect must not call defs.IP()
// (a UDP dial, outside the lab's model; it panics without a route). The test
// runs Connect on a thread in a new network namespace that has only loopback
// (no default route), against a fake master and one replica listener there.
func TestIssueU1_ConnectWithoutRoute(t *testing.T) {
	if defs.LatencyConf != "" {
		t.Fatal("LatencyConf must be empty")
	}
	done := make(chan any, 1)
	go func() {
		runtime.LockOSThread() // never unlocked: the thread exits with the goroutine
		if err := syscall.Unshare(syscall.CLONE_NEWNET); err != nil {
			done <- fmt.Sprintf("skip: unshare(CLONE_NEWNET): %v", err)
			return
		}
		if err := loUp(); err != nil {
			done <- fmt.Sprintf("setup: lo up: %v", err)
			return
		}
		rl, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			done <- fmt.Sprintf("setup: %v", err)
			return
		}
		go func() {
			for {
				if _, err := rl.Accept(); err != nil {
					return
				}
			}
		}()
		ml, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			done <- fmt.Sprintf("setup: %v", err)
			return
		}
		srv := rpc.NewServer()
		srv.RegisterName("Master", &fakeMaster{replicas: []string{rl.Addr().String()}})
		go http.Serve(ml, srv)

		defer func() { done <- recover() }()
		c := NewClientLog("", "127.0.0.1", ml.Addr().(*net.TCPAddr).Port, true, false, false, &dlog.Logger{})
		if err := c.Connect(); err != nil {
			panic(fmt.Sprintf("Connect: %v", err))
		}
		if c.readers[0] == nil || c.dt != nil {
			panic("Connect: no connection to the replica, or a latency table")
		}
	}()
	p := <-done
	if s, ok := p.(string); ok && len(s) > 5 && s[:5] == "skip:" {
		t.Skip(s)
	}
	if p != nil {
		t.Fatalf("Connect without a route: %v", p)
	}
}
