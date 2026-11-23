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
	The proxy package defines the proxy/application layer of a server. The proxy connects to one or more Rabia clients
	to send and receive client requests. It also executes client commands decided by consensus instance(s). For these
	two reasons, it has two primary routines that run concurrently, one is CmdReceiver (client command receiver), and
	the other is KVSExecutor (KV-store executor).
*/
package proxy

import (
	"context"
	"fmt"
	"github.com/go-redis/redis/v8"
	"github.com/rs/zerolog"
	"os"
	"rabia/internal/config"
	"rabia/internal/ledger"
	"rabia/internal/logger"
	"rabia/internal/message"
	"rabia/internal/tcp"
	"sync"
	"time"
)

/*
	A Rabia proxy
*/
type Proxy struct {
	SvrId uint32
	Wg    *sync.WaitGroup
	Done  chan struct{}

	ClientsIn chan message.Command
	ToNet     chan message.Msg
	NetIn     chan message.Msg

	TCP *tcp.ProxyTCP

	KVStore     map[string]string
	RedisClient *redis.Client
	RedisCtx    context.Context

	executeCmdFunc      func(string) string
	executeAndReplyFunc func()

	Logger  zerolog.Logger // the proxy-level log that helps to ensure correctness
	LogFile *os.File       // the log file that should be called .Sync() method before the routine exits

	Ledger    ledger.Ledger
	CurrDec   *message.ConsensusObj // the current decision
	CurrInsId int
	CurrSeq   uint32
}

/*
	Initialize a Rabia proxy
*/
func ProxyInit(svrId uint32, done chan struct{}, doneWg *sync.WaitGroup, proxyIp string,
	toProxy chan message.Command, toNet, netIn chan message.Msg, ledger ledger.Ledger) *Proxy {
	zerologger, logFile := logger.InitLogger("proxy", svrId, 0, "file")
	p := &Proxy{
		SvrId: svrId,
		Wg:    doneWg,
		Done:  done,

		ClientsIn: toProxy,
		ToNet:     toNet,
		NetIn:     netIn,

		TCP: tcp.ProxyTcpInit(svrId, proxyIp, toProxy),

		KVStore:     make(map[string]string),
		RedisClient: RedisInit(svrId),
		RedisCtx:    context.Background(),

		Logger:  zerologger,
		Ledger:  ledger,
		LogFile: logFile,
	}

	/*
		The purpose of these function pointers is to reduce branching on the critical path
	*/
	switch config.Conf.StorageMode {
	case 0: // default: use the dictionary KV Store, no Redis function involved
		p.executeCmdFunc = p.naiveExecuteCmd
		p.executeAndReplyFunc = p.singleExecuteAndReply
	case 1:
		p.executeCmdFunc = p.redisExecuteCmd
		p.executeAndReplyFunc = p.singleExecuteAndReply
	case 2:
		p.executeCmdFunc = nil // not used
		p.executeAndReplyFunc = p.batchExecuteAndReply
	default:
		panic("storage mode (Conf.StorageMode) not supported")
	}

	return p
}

/*
	1. establish proxy-layer TCP connection(s)
*/
func (p *Proxy) Prologue() {
	p.TCP.Connect()
}

/*
	1. sync the log file
	2. close proxy-layer TCP connection(s)
*/
func (p *Proxy) Epilogue() {
	if p.LogFile != nil { // VERIFICATION WORKAROUND (G4): no log file
		if err := p.LogFile.Sync(); err != nil {
			panic(fmt.Sprint("error syncing file", err))
		}
	}
	p.TCP.Close()
}

/*
	Proxy-level main thread 1: receive commands from clients, batch them, and then send to the network layer
*/
func (p *Proxy) CmdReceiver() {
	defer p.Wg.Done()
	batchClock := time.NewTicker(config.Conf.ProxyBatchTimeout)
	defer batchClock.Stop() // release the resources

	CliIds := make([]uint32, config.Conf.ProxyBatchSize)
	CliSqs := make([]uint32, config.Conf.ProxyBatchSize)
	Values := make([]string, config.Conf.ProxyBatchSize*config.Conf.ClientBatchSize)
	IdsSqsCtr := 0
	ValuesCtr := 0
	ProSeq := 0

	// VERIFICATION WORKAROUND (G1): no label (Goose does not translate labeled statements); the same control flow
	for {
		select {

		case <-p.Done:
			return

		case msg := <-p.ClientsIn: // a client's request object
			CliIds[IdsSqsCtr] = msg.CliId
			CliSqs[IdsSqsCtr] = msg.CliSeq
			IdsSqsCtr++
			for _, v := range msg.Commands {
				Values[ValuesCtr] = v
				ValuesCtr++
			}
			if IdsSqsCtr == config.Conf.ProxyBatchSize {
				obj := message.ConsensusObj{ProId: p.SvrId, ProSeq: uint32(ProSeq),
					CliIds: CliIds, CliSeqs: CliSqs, Commands: Values}
				p.ToNet <- message.Msg{Type: message.ClientRequest, Obj: &obj}
				CliIds = make([]uint32, config.Conf.ProxyBatchSize)
				CliSqs = make([]uint32, config.Conf.ProxyBatchSize)
				Values = make([]string, config.Conf.ProxyBatchSize*config.Conf.ClientBatchSize)
				IdsSqsCtr = 0
				ValuesCtr = 0
				ProSeq++
			}

		case _ = <-batchClock.C: // time-based proxy batch
			if IdsSqsCtr != 0 {
				obj := message.ConsensusObj{ProId: p.SvrId, ProSeq: uint32(ProSeq),
					CliIds: CliIds[:IdsSqsCtr], CliSeqs: CliSqs[:IdsSqsCtr], Commands: Values[:ValuesCtr]}
				p.ToNet <- message.Msg{Type: message.ClientRequest, Obj: &obj}
				CliIds = make([]uint32, config.Conf.ProxyBatchSize)
				CliSqs = make([]uint32, config.Conf.ProxyBatchSize)
				Values = make([]string, config.Conf.ProxyBatchSize*config.Conf.ClientBatchSize)
				IdsSqsCtr = 0
				ValuesCtr = 0
				ProSeq++
			}

		case _ = <-p.NetIn: // dec msg -> reply
			panic("this channel is reserved only, no msg should come in")
		}
	}
}

/*
	Proxy-level main thread 2: check the Ledger to see if there's a new command, apply all new commands in sequence on
	the KV store
*/
func (p *Proxy) KVSExecutor() {
	defer p.Wg.Done()
	for {
		select {
		case <-p.Done:
			return
		default:
			slot := p.CurrSeq % config.Conf.LenLedger
			if p.CurrSeq/config.Conf.LenLedger != p.Ledger[slot].Term {
				continue
			}
			// R1-wake: wait for the slot's decision (or a reset) instead of polling the slot
			dec, done, wake := p.Ledger[slot].GetDecisionOrWake()
			if !done {
				select {
				case <-p.Done:
					return
				case <-wake:
				}
				continue
			}
			p.CurrDec = &dec

			if p.CurrDec.IsNull {
				p.Logger.Debug().Uint32("SvrSeq", p.CurrDec.SvrSeq).Bool("IsNull", p.CurrDec.IsNull).Msg("")
				p.CurrSeq++
				continue
			} else {
				p.Logger.Debug().Uint32("SvrSeq", p.CurrDec.SvrSeq).Bool("IsNull", p.CurrDec.IsNull).
					Uint32("ProId", p.CurrDec.ProId).Uint32("ProSeq", p.CurrDec.ProSeq).Msg("")
			}

			p.executeAndReplyFunc()
			p.CurrSeq++
		}
	}
}

/*
	the actual executeCmdFunc depends on Conf.EnableRedis
*/
func (p *Proxy) singleExecuteAndReply() {
	for idx, cid := range p.CurrDec.CliIds {
		res := make([]string, config.Conf.ClientBatchSize)
		for j, cmd := range p.CurrDec.Commands[idx*config.Conf.ClientBatchSize : idx*config.Conf.ClientBatchSize+config.Conf.ClientBatchSize] {
			res[j] = p.executeCmdFunc(cmd) // the actual function depends on Conf.EnableRedis
		}
		if ch := p.TCP.ClientSendChan(cid); ch != nil { // if the client is connected to this proxy
			// todo: check the speed here, how about some global variables
			rep := message.Command{SvrSeq: p.CurrDec.SvrSeq, CliId: cid, CliSeq: p.CurrDec.CliSeqs[idx], Commands: res}
			ch <- rep
		}
	}
}

func (p *Proxy) batchExecuteAndReply() {
	replies := p.RedisBatchExecuteCmd()
	for idx, cid := range p.CurrDec.CliIds {
		if ch := p.TCP.ClientSendChan(cid); ch != nil { // if the client is connected to this proxy
			rep := message.Command{SvrSeq: p.CurrDec.SvrSeq, CliId: cid, CliSeq: p.CurrDec.CliSeqs[idx], Commands: replies[idx]}
			ch <- rep
		}
	}
}

/*
	Execute the KV store command and assemble a reply
*/
func (p *Proxy) naiveExecuteCmd(cmd string) string {
	typ := cmd[0:1]
	key := cmd[1 : 1+config.Conf.KeyLen]
	val := cmd[1+config.Conf.KeyLen:]
	if typ == "0" { // write
		p.KVStore[key] = val
		return "0" + key + "ok"
	} else { // read
		v := p.KVStore[key]
		return "1" + key + v
	}
}
