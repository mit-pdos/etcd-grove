//go:build !rpcmodel

// (The model build needs the kit's codec, registered by examples/quepaxanet, to marshal an answer.)

package raxos

import (
	"bufio"
	"encoding/binary"
	"io"
	"net"
	"testing"
	"time"

	"raxos/common"
	"raxos/proto/client"
)

// TestP4FailedAnswerLeavesNoPartialMessage (finding P4): every message on a proxy's connection back
// to a client is a code byte, then the ClientBatch's 8-byte length and protobuf encoding
// (proto/client/clientwrapper.go), and the client reads them in turn. An answer whose encoding
// fails (protobuf refuses a string that is not valid UTF-8: the answer "0"+key+"ok" to a put
// whose command "0"+key+value is valid UTF-8 while its 8-byte key alone is not) must not leave
// part of a message in the stream: as released, the code byte is written before the encoding is
// attempted and stays, so every later answer on the connection is read out of frame. Here the
// client must still read the next answer, intact.
func TestP4FailedAnswerLeavesNoPartialMessage(t *testing.T) {
	l, err := net.Listen("tcp", "127.0.0.1:0") // the client's listener for connections back
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	conns := make(chan net.Conn, 1)
	go func() {
		c, err := l.Accept()
		if err == nil {
			conns <- c
		}
	}()
	cfg := testConfig()
	cfg.Clients[0].CLIENTPORT = portOf(l.Addr())
	pr := NewProxy(2, cfg, nil, nil, nil, "/tmp/", 50, 1, 20000, false, 0, nil, 1, &ClientBatchStore{}, 0,
		nil, nil, 0, 5, nil, 0, 8, 8, 0)
	pr.connectToClient(21)
	c := <-conns
	defer c.Close()

	// the put "0"+key+value: key "aaaaaaa\xc3" (not valid UTF-8 alone), value "\xa9v" (the command
	// is valid UTF-8: "\xc3\xa9" is "é"); its answer "0"+key+"ok" is not valid UTF-8
	bad := common.RPCPair{Code: 1, Obj: &client.ClientBatch{Sender: 21, Id: "21.0",
		Messages: []*client.ClientBatch_SingleMessage{{Message: "0aaaaaaa\xc3ok"}}}}
	good := common.RPCPair{Code: 1, Obj: &client.ClientBatch{Sender: 21, Id: "21.1",
		Messages: []*client.ClientBatch_SingleMessage{{Message: "1key00000nil"}}}}
	pr.internalSendMessage(21, bad)
	pr.internalSendMessage(21, good)

	// the client, as examples/quepaxanet's receive reads it: the handshake, then messages
	c.SetReadDeadline(time.Now().Add(5 * time.Second))
	rd := bufio.NewReader(c)
	var hs [4]byte
	if _, err := io.ReadFull(rd, hs[:]); err != nil || binary.LittleEndian.Uint16(hs[:]) != 2 {
		t.Fatalf("handshake: %v %v", hs, err)
	}
	code, err := rd.ReadByte()
	if err != nil || code != 1 {
		t.Fatalf("code byte: %v %v", code, err)
	}
	var lb [8]byte
	if _, err := io.ReadFull(rd, lb[:]); err != nil {
		t.Fatal(err)
	}
	if n := binary.LittleEndian.Uint64(lb[:]); n > 1<<20 {
		t.Fatalf("the answer after a failed one is read out of frame: length %d (bytes %v)", n, lb)
	}
	b := &client.ClientBatch{}
	rd2 := io.MultiReader(bytesReader(lb[:]), rd)
	if err := b.Unmarshal(rd2); err != nil {
		t.Fatalf("the answer after a failed one does not decode: %v", err)
	}
	if b.Id != "21.1" || len(b.Messages) != 1 || b.Messages[0].Message != "1key00000nil" {
		t.Fatalf("the client read %v, not the answer sent", b)
	}
}

type byteReader struct{ b []byte }

func (r *byteReader) Read(p []byte) (int, error) {
	if len(r.b) == 0 {
		return 0, io.EOF
	}
	n := copy(p, r.b)
	r.b = r.b[n:]
	return n, nil
}

func bytesReader(b []byte) io.Reader { return &byteReader{b} }
