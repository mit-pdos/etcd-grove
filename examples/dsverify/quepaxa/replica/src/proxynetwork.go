package raxos

import (
	"bufio"
	"encoding/binary"
	"fmt"
	"io"
	"net"
	"raxos/common"
	"raxos/proto"
	"time"
)

// start listening to the proxy tcp connection, and setup all outgoing wires

func (pr *Proxy) NetworkInit() {
	//pr.debug("proxy network init", -1)
	pr.startOutgoingLinks()
	go pr.waitForConnections()
}

/*
	fill the RPC table by assigning a unique id to each message type
*/

func (pr *Proxy) RegisterRPC(msgObj proto.Serializable, code uint8) {
	pr.rpcTable[code] = &common.RPCPair{code, msgObj}
}

/*
	Listen on the server port for new connections
	Each proxy receives connection from all clients
*/

func (pr *Proxy) waitForConnections() {

	var b [4]byte
	bs := b[:4]
	//pr.debug("Listening to messages on "+pr.serverAddress, 0)
	// listen to proxy port
	for {
		l, err := net.Listen("tcp", pr.serverAddress)
		if err == nil {
			pr.Listener = l
			break
		}
		// the proxy port cannot be listened on yet: try again
		time.Sleep(100 * time.Millisecond)
	}

	for true {
		conn, err := pr.Listener.Accept()
		if err != nil {
			// a failed accept is a fault of the network, not of the replica: accept the next
			fmt.Println("TCP accept error:", err)
			continue
		}
		if _, err := io.ReadFull(conn, bs); err != nil {
			// the connection broke before its handshake arrived: drop it
			fmt.Println("Connection id reading error:", err)
			conn.Close()
			continue
		}
		id := int32(binary.LittleEndian.Uint16(bs))
		//pr.debug("Received incoming tcp connection from "+strconv.Itoa(int(id)), -1)

		pr.incomingClientReaders[int64(id)] = bufio.NewReader(conn)
		go pr.connectionListener(pr.incomingClientReaders[int64(id)], id)
		//pr.debug("Started listening to "+strconv.Itoa(int(id)), -1)
		pr.connectToClient(id) // make a TCP connection with client id
	}
}

/*
	listen to a given connection. Upon receiving any message, put it into the central buffer
*/

func (pr *Proxy) connectionListener(reader *bufio.Reader, id int32) {

	var msgType uint8
	var err error = nil

	for true {
		if msgType, err = reader.ReadByte(); err != nil {
			//pr.debug("Error while reading code byte: the TCP connection was broken for "+strconv.Itoa(int(id)), 0)
			return
		}
		if rpair, present := pr.rpcTable[msgType]; present {
			obj := rpair.Obj.New()
			if err = obj.Unmarshal(reader); err != nil {
				//pr.debug("Error while unmarshalling", 0)
				return
			}
			pr.incomingChan <- common.RPCPair{
				Code: msgType,
				Obj:  obj,
			}
		} else {
			//pr.debug("Error: received unknown message type", 0)
			return
		}
	}
}

/*
	make a TCP connection to the client id
*/

func (pr *Proxy) connectToClient(id int32) {
	var b [4]byte
	bs := b[:4]
	for true {
		conn, err := net.Dial("tcp", pr.clientAddrList[int64(id)])
		if err == nil {
			binary.LittleEndian.PutUint16(bs, uint16(pr.name))
			_, err := conn.Write(bs)
			if err != nil {
				//pr.debug("Error connecting to client "+strconv.Itoa(int(id)), 0)
				// the connection broke: dial again
				conn.Close()
				continue
			}
			// the connection starts with the handshake: only now may answers be written to it
			pr.clientWritersMutex.Lock()
			pr.outgoingClientWriters[int64(id)] = bufio.NewWriter(conn)
			pr.clientWritersMutex.Unlock()
			//pr.debug("Started outgoing tcp connection to client "+strconv.Itoa(int(id)), -1)
			break
		}
	}

}

/*
	write a message to the wire, first the message type is written and then the actual message
*/

func (pr *Proxy) internalSendMessage(peer int64, rpcPair common.RPCPair) {

	//pr.debug("proxy internal sending message to  "+strconv.Itoa(int(peer)), 0)

	code := rpcPair.Code
	msg := rpcPair.Obj

	var w *bufio.Writer

	pr.clientWritersMutex.Lock()
	w = pr.outgoingClientWriters[peer]
	pr.clientWritersMutex.Unlock()
	if w == nil {
		// the client has not been dialed back yet: the answer cannot be sent
		return
	}
	// encode the message first: a message is its code byte, then its length and encoding, so one
	// that cannot be encoded is not sent, and leaves nothing on the wire
	var enc msgBuffer
	if msg.Marshal(&enc) != nil {
		//pr.debug("Error while marshalling", 0)
		return
	}
	pr.buffioWriterMutexes[peer].Lock()

	err := w.WriteByte(code)
	if err != nil {
		//pr.debug("Error while writing byte", 0)
		pr.buffioWriterMutexes[peer].Unlock()
		return
	}
	_, err = w.Write(enc.b)
	if err != nil {
		//pr.debug("Error while writing the message", 0)
		pr.buffioWriterMutexes[peer].Unlock()
		return
	}
	err = w.Flush()
	if err != nil {
		//pr.debug("Error while flushing", 0)
		pr.buffioWriterMutexes[peer].Unlock()
		return
	}
	pr.buffioWriterMutexes[peer].Unlock()

	//pr.debug("proxy sent internal sending message to  "+strconv.Itoa(int(peer)), -1)

}

/*
	a set of threads that manages outgoing messages: write the message to the OS buffers
*/

func (pr *Proxy) startOutgoingLinks() {
	for i := 0; i < 200; i++ { // 200 is the number of threads
		go func() {
			for true {
				outgoingMessage := <-pr.outgoingMessageChan
				pr.internalSendMessage(outgoingMessage.Peer, *outgoingMessage.RpcPair)
				//pr.debug("proxy called internal send", 0)
			}
		}()
	}
}

/*
	adds a new out going message to the out going channel
    note that the message object inside the RPC pair should be unique because the protobuf objects are not thread safe
*/

func (pr *Proxy) sendMessage(peer int64, rpcPair common.RPCPair) {
	pr.outgoingMessageChan <- common.OutgoingRPC{
		RpcPair: &rpcPair,
		Peer:    peer,
	}
	//pr.debug("proxy added a new outgoing message  ", -1)
}

// msgBuffer is an io.Writer that keeps the bytes written to it: a message's length and encoding,
// before the message is sent
type msgBuffer struct {
	b []byte
}

func (m *msgBuffer) Write(p []byte) (int, error) {
	m.b = append(m.b, p...)
	return len(p), nil
}
