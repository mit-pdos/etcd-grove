package consensus

// Tests of the consensus instance's shared slot state (findings R1-R4 of the rabia-net verification; see the
// verification project's issues/). The race tests fail under the race detector before the fix (go test -race).

import (
	"sync"
	"testing"
	"time"

	"rabia/internal/config"
	"rabia/internal/ledger"
	"rabia/internal/message"
	"rabia/roles/server/layers/proxy"
)

var confOnce sync.Once

func testConf(t *testing.T) {
	confOnce.Do(func() { setConf() })
}

func setConf() {
	config.Conf.NServers = 3
	config.Conf.NFaulty = 1
	config.Conf.NClients = 6
	config.Conf.ClientBatchSize = 1
	config.Conf.ProxyBatchSize = 1
	config.Conf.LogLevel = "warn"
	config.Conf.ProjectFolder = "/tmp/rabia-net-test"
	config.Conf.CalcConstants()
	config.Conf.LenLedger = 4
	config.Conf.StorageMode = 0
}

func testInstance(t *testing.T) *Consensus {
	testConf(t)
	l := make(ledger.Ledger, config.Conf.LenLedger)
	for i := range l {
		l[i] = &ledger.Slot{}
		l[i].Reset()
	}
	ch := func() chan message.Msg { return make(chan message.Msg, 100) }
	return ConsensusInit(0, 0, make(chan struct{}), &sync.WaitGroup{}, ch(), ch(), ch(), ch(), l)
}

func obj(proId, proSeq uint32) message.ConsensusObj {
	return message.ConsensusObj{ProId: proId, ProSeq: proSeq, CliIds: []uint32{0}, CliSeqs: []uint32{0},
		Commands: []string{"1key00000"}}
}

// R1: the proxy's executor reads a slot's decision while the consensus executor's epilogue writes it.
func TestRaceProxyReadsDecision(t *testing.T) {
	c := testInstance(t)
	p := proxy.ProxyInit(0, c.Done, &sync.WaitGroup{}, "127.0.0.1:0", make(chan message.Command), c.ConExecutorToNet,
		c.NetToMsgHandler, c.Ledger)
	defer p.TCP.Listener.Close()
	p.Wg.Add(1)
	go p.KVSExecutor()
	time.Sleep(10 * time.Millisecond)
	c.SvrSeq = 0
	c.Ledger[0].SetMyProposal(obj(1, 0))
	c.epilogue(0, message.ConsensusObj{IsNull: true})
	time.Sleep(10 * time.Millisecond)
	close(c.Done)
	p.Wg.Wait()
}

// R2: the message handler reads IsDone and writes HasRecvDec while the executor reads HasRecvDec (wait) and writes
// IsDone (epilogue).
func TestRaceHandlerExecutorFlags(t *testing.T) {
	for k := 0; k < 50; k++ {
		c := testInstance(t)
		c.Ledger[0].SetMyProposal(obj(1, 0))
		c.Ledger[0].Round = 1
		a, b, d := obj(2, 0), obj(2, 0), obj(2, 0)
		c.binConMsgHandling(message.Msg{Type: message.Proposal, Obj: &a})
		c.binConMsgHandling(message.Msg{Type: message.Proposal, Obj: &b}) // a Proposal notification
		done := make(chan struct{})
		go func() {
			defer close(done)
			c.binConMsgHandling(message.Msg{Type: message.Decision, Obj: &d}) // writes HasRecvDec
			c.binConMsgHandling(message.Msg{Type: message.Decision, Obj: &d}) // reads IsDone
		}()
		if c.wait(0) { // reads HasRecvDec for the Proposal notification
			c.wait(0) // the decision: epilogue writes IsDone
		}
		<-done
	}
}

// R4: the message handler, answering a ProposalRequest, sorts the slot's proposals while the executor reads and
// sorts them.
func TestRaceProposalsSorted(t *testing.T) {
	for k := 0; k < 20; k++ {
		c := testInstance(t)
		a, b := obj(2, 0), obj(1, 0)
		c.binConMsgHandling(message.Msg{Type: message.Proposal, Obj: &a})
		c.binConMsgHandling(message.Msg{Type: message.Proposal, Obj: &b})
		c.Wg.Add(1)
		go c.MsgHandler()
		c.NetToMsgHandler <- message.Msg{Type: message.ProposalRequest, Phase: 1, Value: 0}
		c.phase0Round1AfterWait(0)
		close(c.Done)
		c.Wg.Wait()
	}
}

// R3: a slot may run past phase LenBlockArray - 1 (the binary consensus has no bound on phases): the message
// handler records a peer's state and vote of any phase, the executor its own, and the epilogue counts the rounds.
func TestPhasesBeyondBlockArray(t *testing.T) {
	c := testInstance(t)
	p := uint32(config.Conf.LenBlockArray) + 2
	o := message.ConsensusObj{SvrSeq: 0}
	c.binConMsgHandling(message.Msg{Type: message.State, Phase: p, Value: 1, Obj: &o})
	c.binConMsgHandling(message.Msg{Type: message.Vote, Phase: p, Value: 1, Obj: &o})
	c.Ledger[0].SetMyBCMsgs(p, 1, 1)
	c.Ledger[0].Phase = p
	c.Ledger[0].Round = 2
	if c.Ledger[0].RecvBCMsgsMajT(p, 2) != 1 || c.Ledger[0].GetMyBCMsgs(p, 1) != 1 {
		t.Fatalf("phase %d: messages not recorded", p)
	}
	c.Ledger[0].SetMyProposal(obj(1, 0))
	c.epilogue(0, message.ConsensusObj{IsNull: true})
}

// VERIFICATION WORKAROUND G8: idSeqKey identifies consensus objects as GetIdSeq did.
func TestIdSeqKeyAsGetIdSeq(t *testing.T) {
	vals := []uint32{0, 1, 2, 9, 10, 11, 99, 100, 101, 1 << 31, 1<<32 - 1}
	for _, a := range vals {
		for _, b := range vals {
			for _, c := range vals {
				for _, d := range vals {
					x, y := message.ConsensusObj{ProId: a, ProSeq: b}, message.ConsensusObj{ProId: c, ProSeq: d}
					if (x.GetIdSeq() == y.GetIdSeq()) != (idSeqKey(&x) == idSeqKey(&y)) {
						t.Fatalf("%v %v", x, y)
					}
				}
			}
		}
	}
}

// N9: a slot's phase is a uint32; the binary consensus runs phases until it decides (no bound), and
// phase p+1 follows phase p. At phase 2^32-1 the next phase cannot be represented: the executor must
// not wrap to phase 0 (it would overwrite its own phase-0 state and broadcast states of phase 0).
func TestPhaseDoesNotWrap(t *testing.T) {
	c := testInstance(t)
	c.ResetCommonCoin() // as Prologue does
	c.Ledger[0].Phase = 0xffffffff
	c.Ledger[0].Round = 2
	c.Ledger[0].SetMyBCMsgs(0, 1, 7) // a marker in phase 0's own state
	done := make(chan struct{})
	go func() {
		c.phaseNRound2AfterWait(0)
		close(done)
	}()
	select {
	case <-done:
		t.Fatalf("phase %d: the executor went on (phase now %d, phase 0 state %d)", uint32(0xffffffff),
			c.Ledger[0].Phase, c.Ledger[0].GetMyBCMsgs(0, 1))
	case <-time.After(100 * time.Millisecond):
	}
	close(c.Done)
	<-done
	if c.Ledger[0].Phase != 0xffffffff || c.Ledger[0].GetMyBCMsgs(0, 1) != 7 {
		t.Fatalf("phase wrapped: phase %d, phase 0 state %d", c.Ledger[0].Phase, c.Ledger[0].GetMyBCMsgs(0, 1))
	}
}

// R1-wake: the proxy's executor, waiting for a slot's decision, takes it when the epilogue records it, and returns when
// the server is done while it waits.
func TestProxyWakesOnDecision(t *testing.T) {
	c := testInstance(t)
	p := proxy.ProxyInit(0, c.Done, &sync.WaitGroup{}, "127.0.0.1:0", make(chan message.Command), c.ConExecutorToNet,
		c.NetToMsgHandler, c.Ledger)
	defer p.TCP.Listener.Close()
	p.Wg.Add(1)
	go p.KVSExecutor()
	time.Sleep(10 * time.Millisecond)
	c.SvrSeq = 0
	c.Ledger[0].SetMyProposal(obj(1, 0))
	c.epilogue(0, message.ConsensusObj{IsNull: true})
	deadline := time.Now().Add(5 * time.Second)
	for {
		if p.Ledger[0].GetIsDone() {
			break
		}
		if time.Now().After(deadline) {
			t.Fatal("slot 0 not decided")
		}
		time.Sleep(time.Millisecond)
	}
	time.Sleep(20 * time.Millisecond) // the executor applies slot 0 and waits on slot 1
	close(c.Done)
	p.Wg.Wait()
	if p.CurrSeq != 1 {
		t.Fatalf("the executor did not take slot 0's decision: CurrSeq=%d", p.CurrSeq)
	}
}
