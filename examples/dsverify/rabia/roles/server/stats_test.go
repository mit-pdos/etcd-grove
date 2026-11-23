package server

// Test of the server's terminal logger (finding S1 of the rabia-net verification; see the verification project's
// issues/): it reads the proxy's client table and the consensus executor's slot counters while they change. Fails
// under the race detector before the fix (go test -race).

import (
	"sync"
	"testing"
	"time"

	"rabia/internal/config"
	"rabia/internal/message"
)

// the configuration is set once: routines of an earlier run (go test -count) may still read it
var confOnce sync.Once

func TestRaceTerminalLoggerReadsCounters(t *testing.T) {
	confOnce.Do(func() {
		config.Conf.NServers = 3
		config.Conf.NFaulty = 1
		config.Conf.NClients = 6
		config.Conf.ClientBatchSize = 1
		config.Conf.ProxyBatchSize = 1
		config.Conf.LogLevel = "warn"
		config.Conf.ProjectFolder = "/tmp/rabia-net-test"
		config.Conf.CalcConstants()
		config.Conf.StorageMode = 0
		config.Conf.SvrLogInterval = time.Millisecond
		config.Conf.Peers = []string{"127.0.0.1:1", "127.0.0.1:2", "127.0.0.1:3"}
	})
	s := ServerInit(0, "127.0.0.1:0", "127.0.0.1:0")
	go s.TerminalLogger()
	s.Wg.Add(2)
	go s.Consensus.MsgHandler()
	go s.Consensus.Executor()
	go func() { // the network layer's side: drop what the executor sends
		for {
			select {
			case <-s.ConExecutorToNet:
			case <-s.Done:
				return
			}
		}
	}()
	for i := uint32(0); i < 50; i++ {
		o := message.ConsensusObj{ProId: 1, ProSeq: i, CliIds: []uint32{0}, CliSeqs: []uint32{i},
			Commands: []string{"1key00000"}}
		s.NetToMsgHandler <- message.Msg{Type: message.ClientRequest, Obj: &o}
		d := o
		d.SvrSeq = i
		s.NetToMsgHandler <- message.Msg{Type: message.Decision, Obj: &d}
		time.Sleep(time.Millisecond)
	}
	close(s.Done)
}
