package epaxos

import (
	"bytes"
	"os"
	"os/exec"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos-epaxos/config"
	"github.com/imdea-software/swiftpaxos-epaxos/dlog"
	"github.com/imdea-software/swiftpaxos-epaxos/state"
)

// TestRunLoopAndExecutorDoNotRace runs a replica built by New (its run loop, its executor) in a
// child process of this test binary, under the race detector, and feeds its run loop Commits
// (handleCommit creates and fills instances that the executor reads and executes),
// recovery requests (startRecoveryForInstance reads IsLeader) and BeTheLeader calls (an rpc
// goroutine writes IsLeader). The child is a single replica (N = 1: no peers to connect to;
// ComputeClosestPeers takes its 10 s). The parent's run loop and executor share the instances
// with no synchronization: the race detector reports a data race. A child process keeps the
// replica's goroutines (which never stop) away from the other tests.
func TestRunLoopAndExecutorDoNotRace(t *testing.T) {
	if os.Getenv("EPAXOS_E1_CHILD") == "1" {
		raceChild()
		return
	}
	if !raceEnabled {
		t.Skip("needs the race detector (go test -race)")
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestRunLoopAndExecutorDoNotRace$", "-test.count=1")
	cmd.Env = append(os.Environ(), "EPAXOS_E1_CHILD=1")
	out, err := cmd.CombinedOutput()
	if bytes.Contains(out, []byte("DATA RACE")) || err != nil {
		if len(out) > 6000 {
			out = out[:6000]
		}
		t.Fatalf("the replica's goroutines race (child: %v):\n%s", err, out)
	}
	if !bytes.Contains(out, []byte("E1CHILD k1=v")) {
		t.Fatalf("the child replica did not execute the commands:\n%s", out)
	}
}

func raceChild() {
	r := New("r0", 0, []string{"127.0.0.1:0"}, true, false, false, 0, false, 0, &config.Config{}, &dlog.Logger{})
	time.Sleep(11 * time.Second) // ConnectToPeers, ComputeClosestPeers (20 rounds of 500 ms)
	done := make(chan bool)
	go func() {
		for i := 0; i < 50; i++ {
			r.BeTheLeader(nil, nil)
			time.Sleep(time.Millisecond)
		}
		done <- true
	}()
	for i := int32(0); i < 400; i++ {
		r.commitChan <- &Commit{LeaderId: 0, Replica: 0, Instance: i, Ballot: 0,
			Command: []state.Command{put(int64(i%3), "v")}, Seq: i, Deps: []int32{i - 1}}
		if i%10 == 0 {
			r.instancesToRecover <- &instanceId{0, 100000 + i} // never committed: no Commit is lost to its ballot
		}
		time.Sleep(200 * time.Microsecond)
	}
	<-done
	time.Sleep(200 * time.Millisecond)
	g := get(1)
	os.Stdout.WriteString("E1CHILD k1=" + string(g.Execute(r.State)) + "\n") // under the store's lock
	os.Exit(0)
}
