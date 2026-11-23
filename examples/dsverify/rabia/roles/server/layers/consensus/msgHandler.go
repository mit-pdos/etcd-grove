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
package consensus

import (
	"rabia/internal/config"
	"rabia/internal/message"
)

/*
    The MsgHandler routine does not forward each of Proposal, State, Vote, and Decision messages directly to the
    Executor. Instead, after gathering strictly n - f messages for each round (see where HasEnoughMsg is called),
    it then notifies the Executor. MsgHandler ignores future messages for this round to make sure the majority value
    is stable after notifying the Executor.
*/
func (c *Consensus) MsgHandler() {
	defer c.Wg.Done()
	// VERIFICATION WORKAROUND (G1): no label (Goose does not translate labeled statements); the same control flow
	for {
		select {
		case <-c.Done:
			return
		case msg := <-c.NetToMsgHandler:
			switch msg.Type {
			case message.ClientRequest:
				c.QPush(*msg.Obj) // push the object to the pending request queue
			case message.ProposalRequest:
				/*
                    msg.Value contains the sequence number of the message, we are testing whether the term of the
                    message is the same as the term of the Slot object
                */
				if msg.Value >= config.Conf.LenLedger { // SCOPE GUARD (see getRequest): no slot is reused
					continue
				}
				if !c.IsTermMatched(msg.Value) {
					continue
				}
				/*
                    Maybe you wonder there's a potential race? see out comments in "Race Conditions Documented" in
                    consensus.go.
                */
				slot := msg.Value % config.Conf.LenLedger
				if c.Ledger[slot].HasEnoughMsg(0, 1) {
					if c.Ledger[slot].RecvProposalsMajT() >= config.Conf.Majority {
						c.MsgHandlerToNet <- c.genProposalReply(msg.Value, msg.Phase)
					}
				}
			case message.Proposal, message.State, message.Vote, message.Decision:
				c.binConMsgHandling(msg)
			default: // ProposalReply should never be received by MsgHandler
				panic("should not happen, this msg type should not go to MsgHandler")
			}
		}
	}
}

/*
    Handles Proposal, State, Vote, and Decision messages
*/
func (c *Consensus) binConMsgHandling(msg message.Msg) {
	seq := msg.Obj.SvrSeq
	if seq >= config.Conf.LenLedger { // SCOPE GUARD (see getRequest): no slot is reused
		return
	}
	if ok := c.UpdateTermIfNecessary(seq, false); !ok {
		c.OlderThanTermMsg++
		return
	}
	slot := seq % config.Conf.LenLedger
	Phase := msg.Phase
	Value := msg.Value
	if c.Ledger[slot].GetIsDone() {
		return
	}
	switch msg.Type {
	case message.Proposal:
		if c.Ledger[slot].HasEnoughMsg(0, 1) {
			return
		}
		c.Ledger[slot].PutRecvProposals(*msg.Obj)
		if c.Ledger[slot].HasEnoughMsg(0, 1) {
			out := message.Msg{Phase: 0, Type: message.Proposal, Value: seq}
			c.Ledger[slot].Queue <- out
		}

	case message.State:
		if c.Ledger[slot].HasEnoughMsg(Phase, 1) {
			return
		}
		c.Ledger[slot].PutRecvBCMsgs(Phase, 1, Value)
		if c.Ledger[slot].HasEnoughMsg(Phase, 1) {
			out := message.Msg{Phase: Phase, Type: message.State, Value: seq}
			c.Ledger[slot].Queue <- out
		}

	case message.Vote:
		if c.Ledger[slot].HasEnoughMsg(Phase, 2) {
			return
		}
		c.Ledger[slot].PutRecvBCMsgs(Phase, 2, Value)
		if c.Ledger[slot].HasEnoughMsg(Phase, 2) {
			out := message.Msg{Phase: Phase, Type: message.Vote, Value: seq}
			c.Ledger[slot].Queue <- out
		}

	case message.Decision:
		if !c.Ledger[slot].GetHasRecvDec() {
			c.Ledger[slot].Queue <- msg
			c.Ledger[slot].SetHasRecvDec()
		}
	}

}
