/*
    Copyright 2021 Rabia Research Team and Developers

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.
*/
/*
    The server package defines a Rabia server's struct and its initialization, preparation, and main function. Note: A
    server has many Goroutines, and each routine belongs to one of the three server layers: the proxy/application layer,
    the peer-communicating network layer, and the consensus instance layer. There are one or two main Go routines at
    each layer. When a server wants to exit, it needs to wait for them all. Besides, the proxy and network layers
    maintain their TCP connections, which require a few more Goroutines to send requests and to wait for responses.
*/
package server

import (
	"fmt"
	"github.com/rs/zerolog"
	"os"
	"rabia/internal/config"
	"rabia/internal/ledger"
	"rabia/internal/logger"
	"rabia/internal/message"
	"rabia/internal/system"
	"rabia/roles/server/layers/consensus"
	"rabia/roles/server/layers/network"
	"rabia/roles/server/layers/proxy"
	"sync"
	"time"
)

/*
    A Rabia server
*/
type Server struct {
	SvrId uint32
	Wg    *sync.WaitGroup
	Done  chan struct{}

	Ledger  []*ledger.Slot
	Logger  zerolog.Logger // the real-time server log that help to track throughput and the number of connections
	LogFile *os.File       // the log file that should be called .Sync() method before the routine exits,
	// see the last a few lines of Executor.Executor() function for an example

	Proxy     *proxy.Proxy
	Network   *network.Network
	Consensus *consensus.Consensus

	ClientsToProxy                    chan message.Command
	ProxyToNet, NetToProxy            chan message.Msg
	MsgHandlerToNet, ConExecutorToNet chan message.Msg
	NetToMsgHandler, NetToConExecutor chan message.Msg
}

/*
    Initialize a server -- go channels and routine allocations

    Difference between *Init() functions and *Prepare/Prologue()  functions in the Rabia project:
    *Init(): allocating objects, does not involve the network activity (except allocating a listener)
    *Prepare/Prologue(): involves the network activity and starts to listen to OS signals
*/
func ServerInit(svrId uint32, proxyIp, netIp string) *Server {
	s := &Server{
		SvrId: svrId,
		Wg:    &sync.WaitGroup{},
		Done:  make(chan struct{}),

		Ledger: make(ledger.Ledger, int(config.Conf.LenLedger)), // VERIFICATION WORKAROUND (G11): an int length (Goose: a uint32 length has no step); the same slice

		ClientsToProxy:   make(chan message.Command),
		ProxyToNet:       make(chan message.Msg, config.Conf.LenChannel),
		NetToProxy:       make(chan message.Msg, config.Conf.LenChannel),
		MsgHandlerToNet:  make(chan message.Msg, config.Conf.LenChannel),
		ConExecutorToNet: make(chan message.Msg, config.Conf.LenChannel),
		NetToMsgHandler:  make(chan message.Msg, config.Conf.LenChannel),
		NetToConExecutor: make(chan message.Msg, config.Conf.LenChannel),
	}
	// s.Logger, s.LogFile =  logger.InitLogger("server", svrId, 0, "both")
	// note: the log file of this logger should be synced! e.g., see the last a few lines of Executor.Executor()

	s.NetToMsgHandler = make(chan message.Msg, config.Conf.LenChannel)
	s.NetToConExecutor = make(chan message.Msg, config.Conf.LenChannel)
	for i := 0; i < int(config.Conf.LenLedger); i++ {
		s.Ledger[i] = &ledger.Slot{}
		s.Ledger[i].Reset()
	}
	s.Proxy = proxy.ProxyInit(svrId, s.Done, s.Wg, proxyIp, s.ClientsToProxy, s.ProxyToNet, s.NetToProxy, s.Ledger)
	s.Network = network.NetworkInit(svrId, s.Done, s.Wg, netIp, s.NetToProxy, s.ProxyToNet, s.MsgHandlerToNet,
		s.ConExecutorToNet, s.NetToMsgHandler, s.NetToConExecutor)
	s.Consensus = consensus.ConsensusInit(svrId, 0, s.Done, s.Wg, s.NetToMsgHandler,
		s.MsgHandlerToNet, s.NetToConExecutor, s.ConExecutorToNet, s.Ledger)
	return s
}

/*
    1. start the OS signal listener
    2. add the number of major routines in Proxy and Network layers to Wg
    3. start the network layer
    4. start the proxy layer
    5. starts a terminal logger
*/
func (s *Server) Prologue() {
	go system.SigListen(s.Done)
	s.Network.Prologue()
	s.Proxy.Prologue()
	go s.TerminalLogger()
}

/*
    1. start the proxy layer (two separate routines)
    2. start the network layer (two separate routines)
    3. start the consensus layer (two separate routines)
    4. wait all layers to finish
*/
func (s *Server) ServerMain() {
	s.Wg.Add(2)
	go s.Proxy.CmdReceiver()
	go s.Proxy.KVSExecutor()

	s.Wg.Add(2)
	go s.Network.MsgRouter()
	go s.Network.MsgSerializer()

	s.Wg.Add(2)
	go s.Consensus.Executor()
	go s.Consensus.MsgHandler()

	<-s.Done
}

/*
    1. calling proxy level exit
    2. calling network level exit
    3. wait major routines are done
*/
func (s *Server) Epilogue() {
	s.Proxy.Epilogue()
	s.Network.Epilogue()
	s.Wg.Wait()
}

/*
    A terminal logger that prints the status of a server to terminal
*/
func (s *Server) TerminalLogger() {
	tLogger, file := logger.InitLogger("server", s.SvrId, 1, "both")
	defer func() {
		if file == nil { // VERIFICATION WORKAROUND (G4): no log file
			return
		}
		if err := file.Sync(); err != nil {
			panic(fmt.Sprint("error syncing file", err))
		}
	}()
	ticker := time.NewTicker(config.Conf.SvrLogInterval)

	lastNotNulls := 0
	lastCBProcessed := 0
	for {
		select {
		case <-s.Done:
			return
		case <-ticker.C:
			proxyConnect := s.Proxy.TCP.NumConns()

			normalSlots, unmatchedSlots, nullSlots, cbProcessed := s.Consensus.SlotStats()
			thisNotNulls := normalSlots + unmatchedSlots
			thisCBProcessed := cbProcessed
			// VERIFICATION WORKAROUND (G9): the throughput is computed only for the log, which writes nothing (G4):
			// math.Round and time.Duration.Seconds have no model in Perennial. It was
			// math.Round(float64((thisCBProcessed-lastCBProcessed)*config.Conf.ClientBatchSize) / config.Conf.SvrLogInterval.Seconds())
			throughput := float64((thisCBProcessed - lastCBProcessed) * config.Conf.ClientBatchSize)
			// items below may not appear in this order, see https://github.com/rs/zerolog/issues/50
			tLogger.Warn().
				Uint32("Svr Id", s.SvrId).
				Int("Client Conn.", proxyConnect).
				Int("Normal Slots", normalSlots).
				Int("Unmatched Slots", unmatchedSlots).
				Int("NULL Slots", nullSlots).
				Int("Interval not-NULL Slots", thisNotNulls-lastNotNulls).
				Float64("Interval throughput (cmd/sec)", throughput).Msg("")
			lastNotNulls = thisNotNulls
			lastCBProcessed = thisCBProcessed
		}
	}
}
