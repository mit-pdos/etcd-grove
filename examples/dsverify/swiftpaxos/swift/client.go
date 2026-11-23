package swift

import (
	"github.com/imdea-software/swiftpaxos/client"
	"github.com/imdea-software/swiftpaxos/replica"
	"github.com/imdea-software/swiftpaxos/replica/defs"
	fastrpc "github.com/imdea-software/swiftpaxos/rpc"
	"github.com/imdea-software/swiftpaxos/state"
)

type Client struct {
	*client.BufferClient

	// the result in each leader's reply, per command and ballot (C4)
	reps      map[CommandId]map[int32]state.Value
	ready     chan struct{}
	ballot    int32
	delivered map[CommandId]struct{}

	SQ        replica.QuorumI
	FQ        replica.QuorumI
	slowPathH map[CommandId]*replica.MsgSet
	fastPathH map[CommandId]*replica.MsgSet

	fixedMajority bool

	// the number of replicas: ballot b's leader is replica b mod n
	n int

	slowPaths   int
	alreadySlow map[CommandId]struct{}

	cs CommunicationSupply
}

func NewClient(b *client.BufferClient, repNum int) *Client {
	c := &Client{
		BufferClient: b,

		reps:      make(map[CommandId]map[int32]state.Value),
		ready:     make(chan struct{}, 1),
		ballot:    -1,
		delivered: make(map[CommandId]struct{}),

		SQ: replica.NewMajorityOf(repNum),
		FQ: replica.NewThreeQuartersOf(repNum),

		slowPathH: make(map[CommandId]*replica.MsgSet),
		fastPathH: make(map[CommandId]*replica.MsgSet),

		fixedMajority: true,

		n: repNum,

		slowPaths:   0,
		alreadySlow: make(map[CommandId]struct{}),
	}

	t := fastrpc.NewTableId(defs.RPC_TABLE)
	initCs(&c.cs, t)
	c.RegisterRPCTable(t)

	if c.fixedMajority {
		// TODO: it has to be the correct majority
		c.FQ = replica.NewMajorityOf(repNum)
	}

	c.Println("SQ:", c.SQ)
	c.Println("FQ:", c.FQ)

	go c.handleMsgs()

	return c
}

func (c *Client) initMsgSets(cmdId CommandId) {
	m, exists := c.slowPathH[cmdId]
	initSlow := !exists || m == nil
	m, exists = c.fastPathH[cmdId]
	initFast := !exists || m == nil

	if !initSlow && !initFast {
		return
	}

	accept := func(msg, leaderMsg interface{}) bool {
		if leaderMsg == nil {
			return true
		}

		leaderFastAck := leaderMsg.(*MFastAck)
		fastAck := msg.(*MFastAck)

		// an ack of the leader's reply's ballot only: a fast ack of ballot b
		// is a pre-accept by ballot b's fast quorum (C3)
		if fastAck.Ballot != leaderFastAck.Ballot {
			return false
		}

		depEq := Dep(fastAck.Dep).Equals(Dep(leaderFastAck.Dep))
		if _, exists := c.alreadySlow[fastAck.CmdId]; !depEq && !exists {
			c.slowPaths++
			c.alreadySlow[fastAck.CmdId] = struct{}{}
		}

		hashEq := SHashesEq(leaderFastAck.Checksum, fastAck.Checksum)
		if !hashEq {
			return false
		}

		return fastAck.Checksum == nil || hashEq
	}

	// The message sets do not return acks to the pool (LT-F1): Add frees an
	// ack it rejects, and its caller (handleLightSlowAck, the MOptAcks arm)
	// then reads it, while the client's readers take pooled acks.
	free := func(msg interface{}) {}

	if initSlow {
		c.slowPathH[cmdId] = c.slowPathH[cmdId].ReinitMsgSet(c.SQ, accept, free, c.handleFastAndSlowAcks)
	}
	if initFast {
		c.fastPathH[cmdId] = c.fastPathH[cmdId].ReinitMsgSet(c.FQ, accept, free, c.handleFastAndSlowAcks)
	}
}

func (c *Client) handleMsgs() {
	for {
		select {
		case m := <-c.cs.replyChan:
			reply := m.(*MReply)
			c.handleReply(reply)

		case m := <-c.cs.acceptChan:
			accept := m.(*MAccept)
			c.handleAccept(accept)

		case m := <-c.cs.fastAckChan:
			fastAck := m.(*MFastAck)
			c.handleFastAck(fastAck, false)

		case m := <-c.cs.fastAckClientChan:
			fastAckClient := m.(*MFastAckClient)
			f := newFastAck()
			f.Replica = fastAckClient.Replica
			f.Ballot = fastAckClient.Ballot
			cmdId := fastAckClient.CmdId
			f.CmdId = cmdId
			f.Checksum = fastAckClient.Checksum
			c.handleFastAck(f, false)

		case m := <-c.cs.lightSlowAckChan:
			lightSlowAck := m.(*MLightSlowAck)
			c.handleLightSlowAck(lightSlowAck)

		case m := <-c.cs.acksChan:
			acks := m.(*MAcks)
			for _, f := range acks.FastAcks {
				c.handleFastAck(copyFastAck(&f), false)
			}
			for _, s := range acks.LightSlowAcks {
				ls := s
				c.handleLightSlowAck(&ls)
			}

		case m := <-c.cs.optAcksChan:
			optAcks := m.(*MOptAcks)
			for _, ack := range optAcks.Acks {
				fastAck := newFastAck()
				fastAck.Replica = optAcks.Replica
				fastAck.Ballot = optAcks.Ballot
				ackCmdId := ack.CmdId
				fastAck.CmdId = ackCmdId
				if _, exists := c.delivered[fastAck.CmdId]; exists {
					continue
				}
				if !IsNilDepOfCmdId(ack.CmdId, ack.Dep) {
					fastAck.Checksum = ack.Checksum
				} else {
					if _, exists := c.alreadySlow[fastAck.CmdId]; !exists {
						c.slowPaths++
						c.alreadySlow[fastAck.CmdId] = struct{}{}
					}
					fastAck.Checksum = nil
				}
				c.handleFastAck(fastAck, false)
				if _, exists := c.delivered[fastAck.CmdId]; !exists && fastAck.Checksum == nil {
					fastAck := copyFastAck(fastAck)
					fastAck.Checksum = nil
					c.initMsgSets(fastAck.CmdId)
					c.slowPathH[fastAck.CmdId].Add(fastAck.Replica, false, fastAck)
				}
			}
		}
	}
}

func (c *Client) handleFastAck(f *MFastAck, fromLeader bool) bool {
	// a quorum is of distinct replicas: ballot b's leader counts once, by
	// its MReply (the leader message), not also by its own fast ack (N4)
	if !fromLeader && f.Replica == replica.Leader(f.Ballot, c.n) {
		return false
	}

	if c.ballot == -1 {
		c.ballot = f.Ballot
	} else if c.ballot < f.Ballot {
		c.ballot = f.Ballot
	} else if c.ballot > f.Ballot {
		return false
	}

	if _, exists := c.delivered[f.CmdId]; exists {
		return false
	}

	c.initMsgSets(f.CmdId)
	c.fastPathH[f.CmdId].Add(f.Replica, fromLeader, f)
	return true
}

func (c *Client) handleLightSlowAck(ls *MLightSlowAck) {
	if _, exists := c.delivered[ls.CmdId]; exists {
		return
	}
	// the leader counts once, by its MReply (N4)
	if ls.Replica == replica.Leader(ls.Ballot, c.n) {
		return
	}

	if _, exists := c.alreadySlow[ls.CmdId]; !exists {
		c.slowPaths++
		c.alreadySlow[ls.CmdId] = struct{}{}
	}

	f := newFastAck()
	f.Replica = ls.Replica
	f.Ballot = ls.Ballot
	cmdId := ls.CmdId
	f.CmdId = cmdId
	f.Checksum = nil
	c.handleFastAck(f, false)
	if _, exists := c.delivered[f.CmdId]; !exists {
		f := copyFastAck(f)
		f.Checksum = nil
		c.initMsgSets(f.CmdId)
		c.slowPathH[f.CmdId].Add(f.Replica, false, f)
	}
}

func (c *Client) handleFastAndSlowAcks(leaderMsg interface{}, msgs []interface{}) {
	if leaderMsg == nil {
		return
	}

	cmdId := leaderMsg.(*MFastAck).CmdId
	if _, exists := c.delivered[cmdId]; exists {
		return
	}
	c.delivered[cmdId] = struct{}{}
	// the result of the leader's reply whose acks completed the quorum (C4)
	val := c.reps[cmdId][leaderMsg.(*MFastAck).Ballot]
	delete(c.reps, cmdId)
	if ReplyHook != nil {
		ReplyHook(c.ClientId, cmdId, val)
	}
	c.RegisterReply(val, cmdId.SeqNum)

	c.Println("Slow Paths:", c.slowPaths)
}

func (c *Client) handleReply(r *MReply) {
	if _, exists := c.delivered[r.CmdId]; exists {
		return
	}
	f := newFastAck()
	f.Replica = r.Replica
	f.Ballot = r.Ballot
	cmdId := r.CmdId
	f.CmdId = cmdId
	f.Checksum = r.Checksum
	byBallot, exists := c.reps[cmdId]
	if !exists {
		byBallot = make(map[int32]state.Value)
		c.reps[cmdId] = byBallot
	}
	byBallot[r.Ballot] = r.Rep
	c.handleFastAck(f, true)
	if _, exists := c.delivered[f.CmdId]; !exists {
		f := copyFastAck(f)
		f.Checksum = nil
		c.initMsgSets(f.CmdId)
		c.slowPathH[f.CmdId].Add(f.Replica, true, f)
	}
}

func (c *Client) handleAccept(a *MAccept) {
	if _, exists := c.delivered[a.CmdId]; exists {
		return
	}
	c.delivered[a.CmdId] = struct{}{}

	delete(c.reps, a.CmdId)
	if ReplyHook != nil {
		ReplyHook(c.ClientId, a.CmdId, a.Rep)
	}
	c.RegisterReply(a.Rep, a.CmdId.SeqNum)
	c.Println("Slow Paths:", c.slowPaths)
}
