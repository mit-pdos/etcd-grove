package proxy

// Test of the proxy's client table (finding P1 of the rabia-net verification; see the verification project's
// issues/): a client may connect at any time, while the proxy's executor replies to the clients connected to it.
// Fails under the race detector before the fix (go test -race).

import (
	"net"
	"sync"
	"testing"
	"time"

	"rabia/internal/config"
	"rabia/internal/ledger"
	"rabia/internal/message"
)

// the configuration is set once: routines of an earlier run (go test -count) may still read it
var confOnce sync.Once

func TestRaceClientConnectsWhileReplying(t *testing.T) {
	confOnce.Do(func() {
		config.Conf.NServers = 3
		config.Conf.NFaulty = 1
		config.Conf.NClients = 6
		config.Conf.ClientBatchSize = 1
		config.Conf.ProxyBatchSize = 1
		config.Conf.LogLevel = "warn"
		config.Conf.ProjectFolder = "/tmp/rabia-net-test"
		config.Conf.CalcConstants()
		config.Conf.LenLedger = 2000
		config.Conf.StorageMode = 0
	})
	l := make(ledger.Ledger, config.Conf.LenLedger)
	for i := range l {
		l[i] = &ledger.Slot{}
		l[i].Reset()
		// slot i decided: client 0's put
		l[i].SetDecision(message.ConsensusObj{ProId: 1, ProSeq: uint32(i), CliIds: []uint32{0}, CliSeqs: []uint32{uint32(i)},
			Commands: []string{"0key00000v"}})
	}
	done := make(chan struct{})
	p := ProxyInit(0, done, &sync.WaitGroup{}, "127.0.0.1:0", make(chan message.Command, 10), make(chan message.Msg, 10),
		make(chan message.Msg, 10), l)
	p.TCP.Connect()
	p.Wg.Add(1)
	go p.KVSExecutor()
	c, err := net.Dial("tcp", p.TCP.Listener.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	data, _ := (&message.Command{CliId: 0}).Marshal()
	if _, err := c.Write(append([]byte{byte(len(data)), 0, 0, 0}, data...)); err != nil {
		t.Fatal(err)
	}
	time.Sleep(200 * time.Millisecond)
	close(done)
	exited := make(chan struct{})
	go func() { p.Wg.Wait(); close(exited) }()
	select {
	case <-exited:
	case <-time.After(5 * time.Second):
		// the executor read Conns[0] set and SendChan[0] not yet set: its reply blocks on a nil channel
		t.Fatal("the proxy's executor is blocked")
	}
}
