package raxos

import (
	"testing"

	"raxos/common"
	"raxos/proto/client"
)

// TestP2AnswerBeforeConnectionBack (finding P2): an answer to a client the proxy has not dialed
// back yet must not end the replica (its writer is not there yet: the answer cannot be sent).
func TestP2AnswerBeforeConnectionBack(t *testing.T) {
	pr := testProxy(2)
	pr.internalSendMessage(21, answer())
}

func answer() common.RPCPair {
	return common.RPCPair{Code: 1, Obj: &client.ClientBatch{Sender: 21, Id: "21.0.0",
		Messages: []*client.ClientBatch_SingleMessage{{Message: "1key00000nil"}}}}
}
