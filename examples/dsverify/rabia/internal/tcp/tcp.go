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
    The tcp package defines ClientTCP, ProxyTCP, and NetTCP objects, which are the TCP communication component of a
    client, a server's proxy layer, and a server network layer, respectively. These objects and their functions help
    establish and maintain TCP connections and let Go routines to listen to SendChan (the channel that queues messages
    to be sent) and forward messages received over TCP to RecvChan (to be subsequently accessed by caller routines).

    Note:

    1. This package assumes Conf is initialized.

    2. This version of TCP endpoints does no support reconfiguration. Reconfiguring a server requires having multiple
    TCP endpoint objects
*/
package tcp

import (
	"bufio"
	"fmt"
	"net"
	"rabia/internal/config"
	"rabia/internal/message"
	"sync"
	"time"
)

/*
    Generates a reader and a writer from a connection.

    Note: I suspect that if we call this function twice, the newly generated reader and writer will replace the
    previously allocated reader and writer. Be aware of any side-effects.
*/
func GetReaderWriter(conn *net.Conn) (*bufio.Reader, *bufio.Writer) {
	/*
        The socket options tune the connection. They fail only for a connection that is already broken or closed; such
        a connection's reads and writes fail too, and its readers and writers handle that (a failed read ends a receive
        routine, a failed write a send routine), so a failed option is not a reason to stop the process.
    */
	_ = (*conn).(*net.TCPConn).SetWriteBuffer(config.Conf.TcpBufSize)
	_ = (*conn).(*net.TCPConn).SetReadBuffer(config.Conf.TcpBufSize)
	_ = (*conn).(*net.TCPConn).SetKeepAlive(true)
	_ = (*conn).(*net.TCPConn).SetKeepAlivePeriod(20 * time.Second)
	reader := bufio.NewReaderSize(*conn, config.Conf.IoBufSize)
	writer := bufio.NewWriterSize(*conn, config.Conf.IoBufSize)
	return reader, writer
}

/*
    Client TCP, each client connects to a single proxy
*/
type ClientTCP struct {
	Id   uint32          // client id
	Wg   *sync.WaitGroup // waits SendHandler and RecvHandler
	Done chan struct{}   // waits SendHandler and RecvHandler

	ProxyAddr string       // the address of a proxy that the client intends to connect to
	RecvChan  chan message.Command // RecvHandler receives Command objects from Reader and then sends to this channel
	SendChan  chan message.Command // SendHandler receives Command objects from this channel and sends to Writer

	Conn   *net.Conn     // the connection to a proxy
	Reader *bufio.Reader // the reader that binds to the Conn object
	Writer *bufio.Writer // the writer that binds to the Conn object
}

/*
    Returns a ClientTCP with channels initialized, but not Conns, Reader, and Writer fields
*/
func ClientTcpInit(Id uint32, ProxyIp string) *ClientTCP {
	c := &ClientTCP{
		Id:   Id,
		Wg:   &sync.WaitGroup{},
		Done: make(chan struct{}),

		ProxyAddr: ProxyIp,
		RecvChan:  make(chan message.Command, config.Conf.LenChannel),
		SendChan:  make(chan message.Command, config.Conf.LenChannel),
	}
	return c
}

func (c *ClientTCP) connect() {
	for {
		conn, err := net.Dial("tcp", c.ProxyAddr)
		if err == nil {
			c.Conn = &conn
			c.Reader, c.Writer = GetReaderWriter(c.Conn)
			cmd := &message.Command{CliId: c.Id}
			err = cmd.MarshalWriteFlush(c.Writer)
			if err == nil {
				break
			}
			// the connection broke before the handshake was sent: dial again, as after a failed dial
			_ = conn.Close()
		}
		time.Sleep(100 * time.Millisecond)
	}
	c.Wg.Add(2)
	go c.RecvHandler()
	go c.SendHandler()
}

func (c *ClientTCP) Connect() {
	go c.connect()
}

/*
    For each message received, send the message to RecvChan.
    RecvHandler exits when the channel is closed.
*/
func (c *ClientTCP) RecvHandler() {
	defer c.Wg.Done()
	readBuf := make([]byte, 4096*100)
	for {
		var cmd message.Command
		err := cmd.ReadUnmarshal(c.Reader, readBuf)
		if err != nil { // TCP connection closed
			return
		}
		c.RecvChan <- cmd
	}
}

/*
    For each message in SendChan, marshal the message and flush its bytes to the TCP connection through Writer before
    it exits (when c.Done channel is closed, SendHandler exits).
    Note:

    1. it is likely that c.Done closes before SendHandler sends every message ever passed in SendChan. In that case,
    some messages are remained in the channel but not sent.

    2. if the receiver has closed its connection, it is likely that no error msg is produced here at the sender; if the
    sender has closed its connection, error indeed happens.
*/
func (c *ClientTCP) SendHandler() {
	defer c.Wg.Done()
	for {
		select {
		case <-c.Done:
			return
		case req := <-c.SendChan:
			err := req.MarshalWriteFlush(c.Writer)
			if err != nil { // TCP connection closed (as RecvHandler)
				return
			}
		}
	}
}

/*
    Prints the connection status.
*/
func (c *ClientTCP) PrintStatus() {
	fmt.Printf("ClientTcp, SvrId=%d, ProxyAddr=%s, Conns.local=%s, Conns.remote=%s\n",
		c.Id, c.ProxyAddr, (*c.Conn).LocalAddr(), (*c.Conn).RemoteAddr())
}

/*
    Closes the connection and waits SendHandler and RecvHandler to exit.
*/
func (c *ClientTCP) Close() {
	_ = (*c.Conn).Close()
	close(c.Done)
	c.Wg.Wait()
}

/*
    Proxy TCP, each proxy connects to one or more clients
*/
type ProxyTCP struct {
	Id   uint32          // proxy id
	Wg   *sync.WaitGroup // waits SendHandlers and RecvHandlers
	Done chan struct{}   // waits SendHandlers and RecvHandlers

	ProxyAddr string
	RecvChan  chan message.Command   // from clients to the proxy
	SendChan  []chan message.Command // from the proxy to clients

	Listener net.Listener
	Conns    []*net.Conn
	Readers  []*bufio.Reader
	Writers  []*bufio.Writer

	/*
        ConnsLock: the client table (Conns, SendChan, Readers, Writers) is written by the accept routine (connect) when
        a client connects, at any time, and read by the proxy's executor (to reply) and the server's terminal logger: it
        is accessed under ConnsLock (an entry, once set, is read by its own send and receive routines too, which start
        after it is set).
    */
	ConnsLock sync.Mutex
}

// Allocates the ProxyTCP object without accepting connections from its clients
func ProxyTcpInit(Id uint32, ProxyIp string, ToProxy chan message.Command) *ProxyTCP {
	listener, err := net.Listen("tcp", ProxyIp)
	for err != nil {
		// as after a failed Dial: wait and listen again (the endpoint serves on this address only)
		time.Sleep(100 * time.Millisecond)
		listener, err = net.Listen("tcp", ProxyIp)
	}

	p := &ProxyTCP{
		Id:   Id,
		Wg:   &sync.WaitGroup{},
		Done: make(chan struct{}),

		ProxyAddr: ProxyIp,
		RecvChan:  ToProxy,
		SendChan:  make([]chan message.Command, config.Conf.NClients), // at most NClients clients can connect to this proxy

		Listener: listener,
		Conns:    make([]*net.Conn, config.Conf.NClients),
		Readers:  make([]*bufio.Reader, config.Conf.NClients),
		Writers:  make([]*bufio.Writer, config.Conf.NClients),
	}
	/*
        Note: SendChan, Conns, Readers, and Writers entries are not initialized at this points.
        Why arrays are of length NClients but not Clients[id]?
        Because the proxy needs to perform quick lookups of clients, see "if p.TCP.Conns[cid] != nil" on proxy.go
    */
	return p
}

// Waits all its clients to connect
func (p *ProxyTCP) connect() {
	// Conf.NClients is an upper bound, but in common cases,
	// a proxy is connected to (Conf.NClients / Conf.NServers) clients
	for i := 0; i < config.Conf.NClients; i++ {
		conn, err := p.Listener.Accept()
		if err != nil {
			//fmt.Printf("ProxyTCP%d: connection accept thread exits\n", Conf.SvrId)
			return
		}

		reader, writer := GetReaderWriter(&conn)
		var req message.Command
		readBuf := make([]byte, 20)
		err = req.ReadUnmarshal(reader, readBuf)
		if err != nil {
			// the connection broke before the client's handshake arrived: drop it, wait for the next one
			_ = conn.Close()
			i--
			continue
		}

		CliId := req.CliId
		p.ConnsLock.Lock()
		if p.Conns[CliId] != nil {
			// the client connected again (its handshake write failed, maybe after the handshake arrived): it uses its
			// new connection only; close the old one (its routines end) and serve the client on the new one
			_ = (*p.Conns[CliId]).Close()
		}
		p.Conns[CliId] = &conn
		p.SendChan[CliId] = make(chan message.Command, config.Conf.LenChannel)
		p.Writers[CliId] = writer
		p.Readers[CliId] = reader
		ch := p.SendChan[CliId]
		p.ConnsLock.Unlock()
		p.Wg.Add(2)
		// this connection's routines get its own reader, writer and channel (a later connection of the client, which
		// replaces the table's entries, has its own routines)
		go p.sendLoop(ch, writer)
		go p.recvLoop(reader)
	}
}

/*
    Proxy's Connect function is asynchronous - it exits early before connection to all clients (but it has a background
    routine that waits connections). The primary purpose of this function is exiting correctly. If we want the proxy to
    exit before connecting to all clients (due to some error or misconfiguration may happened), this function needs to
    be non-blocking ("Listener.Accept()" is blocking).
*/
func (p *ProxyTCP) Connect() {
	go func() { p.connect() }()
}

func (p *ProxyTCP) RecvHandler(from int) {
	// the client's reader now (connect starts recvLoop with the reader of the connection it accepted)
	p.ConnsLock.Lock()
	reader := p.Readers[from]
	p.ConnsLock.Unlock()
	p.recvLoop(reader)
}

// recvLoop receives a client's requests from reader (the receive routine of one connection)
func (p *ProxyTCP) recvLoop(reader *bufio.Reader) {
	defer p.Wg.Done()
	readBuf := make([]byte, 4096*100)
	for {
		var c message.Command
		err := c.ReadUnmarshal(reader, readBuf)
		if err != nil {
			// maybe: TCP connection is closed or receives an ill-formed message
			return
		}
		p.RecvChan <- c
	}
}

func (p *ProxyTCP) SendHandler(to int) {
	// the client's channel and writer now (connect starts sendLoop with those of the connection it accepted)
	p.ConnsLock.Lock()
	ch, writer := p.SendChan[to], p.Writers[to]
	p.ConnsLock.Unlock()
	p.sendLoop(ch, writer)
}

// sendLoop sends the replies of ch through writer (the send routine of one connection)
func (p *ProxyTCP) sendLoop(ch chan message.Command, writer *bufio.Writer) {
	defer p.Wg.Done()
	for {
		select {
		case <-p.Done:
			return
		case c := <-ch:
			err := c.MarshalWriteFlush(writer)
			if err != nil {
				return
			}
		}
	}
}

/*
    Returns the send channel of client cid, or nil if the client is not connected to this proxy.
*/
func (p *ProxyTCP) ClientSendChan(cid uint32) chan message.Command {
	p.ConnsLock.Lock()
	defer p.ConnsLock.Unlock()
	if p.Conns[cid] == nil {
		return nil
	}
	return p.SendChan[cid]
}

/*
    Returns the number of clients connected to this proxy.
*/
func (p *ProxyTCP) NumConns() int {
	p.ConnsLock.Lock()
	defer p.ConnsLock.Unlock()
	n := 0
	for _, c := range p.Conns {
		if c != nil {
			n++
		}
	}
	return n
}

func (p *ProxyTCP) PrintStatus() {
	p.ConnsLock.Lock()
	defer p.ConnsLock.Unlock()
	fmt.Printf("proxyTcp, SvrId=%d, ProxyAddr=%s\n", p.Id, p.ProxyAddr)
	for i := 0; i < config.Conf.NClients; i++ {
		if p.Conns[i] != nil {
			fmt.Printf("\t client id=%d, ip=%s\n", i, (*p.Conns[i]).RemoteAddr())
		}
	}
}

func (p *ProxyTCP) Close() {
	p.ConnsLock.Lock()
	for i := 0; i < config.Conf.NClients; i++ {
		if p.Conns[i] != nil {
			_ = (*p.Conns[i]).Close()
		}
	}
	p.ConnsLock.Unlock()
	close(p.Done)
	_ = p.Listener.Close()
	p.Wg.Wait()
}

/*
    Network Layer TCP endpoints, each Rabia server has exactly one NetTCP struct and one network address (NetAddr
    below). Each server needs to dial to all peers (including itself) to establish send TCP channels, and needs to
    accept connections from all peers (and itself) to establish receive TCP channels.

    For example, when N = 3, each server does the following in Connect initially:
        waits server 0-2 to connect
        connects to server 0-2

    For example, when N = 5, each server does the following in Connect initially:
        waits server 0-4 to connect
        connects to server 0-4
*/
type NetTCP struct {
	Id   uint32
	Done chan struct{}
	Wg   *sync.WaitGroup

	NetAddr  string
	RecvChan chan message.Msg
	SendChan []chan []byte
	/*
        Note: each SendChan is of type "chan []byte" but not "chan Command" because for each message to be broadcasted,
        we only need to serialize once and let each SendHandler sends the serialized array of bytes.
    */

	Listener net.Listener
	RecvConn []*net.Conn
	SendConn []*net.Conn
	Readers  []*bufio.Reader
	Writers  []*bufio.Writer
}

func NetTCPInit(Id uint32, NetIp string) *NetTCP {
	listener, err := net.Listen("tcp", NetIp)
	for err != nil {
		// as after a failed Dial: wait and listen again (the endpoint serves on this address only)
		time.Sleep(100 * time.Millisecond)
		listener, err = net.Listen("tcp", NetIp)
	}
	if len(config.Conf.Peers) != config.Conf.NServers {
		panic(fmt.Sprint("should not happen", err))
	}

	n := &NetTCP{
		Id:   Id,
		Wg:   &sync.WaitGroup{},
		Done: make(chan struct{}),

		NetAddr:  NetIp,
		RecvChan: make(chan message.Msg, config.Conf.LenChannel),
		SendChan: make([]chan []byte, config.Conf.NServers),

		Listener: listener,
		RecvConn: make([]*net.Conn, config.Conf.NServers),
		SendConn: make([]*net.Conn, config.Conf.NServers),
		Readers:  make([]*bufio.Reader, config.Conf.NServers),
		Writers:  make([]*bufio.Writer, config.Conf.NServers),
	}

	/*
        Note: SendChan, RecvConn, SendConn, Readers, Writers entries are not initialized at this points.
    */
	return n
}

// Listens to all peers (and itself), fill in the respective entries in RecvConn and Readers.
func (n *NetTCP) accepting() {
	for i := 0; i < config.Conf.NServers; i++ {
		conn, err := n.Listener.Accept()
		if err != nil {
			// as dialing does after a failed dial: wait and accept again
			time.Sleep(100 * time.Millisecond)
			i--
			continue
		}

		reader, _ := GetReaderWriter(&conn)
		var c message.Command
		readBuf := make([]byte, 20)
		err = c.ReadUnmarshal(reader, readBuf)
		if err != nil {
			// the connection broke before the peer's handshake arrived: drop it; the peer dials again
			_ = conn.Close()
			i--
			continue
		}

		id := c.CliId
		if n.RecvConn[id] != nil {
			// the peer connected again (its handshake write failed, maybe after the handshake arrived): it uses its new
			// connection only; replace the old one, and do not count the peer twice (each peer is accepted once)
			_ = (*n.RecvConn[id]).Close()
			i--
		}
		n.RecvConn[id] = &conn
		n.Readers[id] = reader
	}
}

// Dials to all peers (and itself), fill in the respective entries in SendChan, SendConn, and Writers.
func (n *NetTCP) dialing() {
	if len(config.Conf.Peers) != config.Conf.NServers {
		panic(fmt.Sprint("should not happen, len(Conf.Peers) != Conf.NServers"))
	}
	for i := 0; i < config.Conf.NServers; i++ {
		var conn net.Conn
		var err error
		conn, err = net.Dial("tcp", config.Conf.Peers[i])
		if err != nil {
			time.Sleep(100 * time.Millisecond)
			i--
			continue
		}

		n.SendChan[i] = make(chan []byte, config.Conf.LenChannel)
		n.SendConn[i] = &conn

		_, n.Writers[i] = GetReaderWriter(&conn)

		c := &message.Command{CliId: n.Id}
		err = c.MarshalWriteFlush(n.Writers[i])
		if err != nil {
			// the connection broke before the handshake was sent: dial again, as after a failed dial
			_ = conn.Close()
			time.Sleep(100 * time.Millisecond)
			i--
			continue
		}
	}
}

func (n *NetTCP) Connect() {
	var wg sync.WaitGroup
	wg.Add(2)
	go func() {
		n.accepting()
		wg.Done()
	}()
	go func() {
		n.dialing()
		wg.Done()
	}()
	wg.Wait()

	n.Wg.Add(config.Conf.NServers * 2)
	for i := 0; i < config.Conf.NServers; i++ {
		go n.RecvHandler(i)
		go n.SendHandler(i)
	}
}

func (n *NetTCP) RecvHandler(from int) {
	defer n.Wg.Done()
	readBuf := make([]byte, config.Conf.IoBufSize)
	for {
		var m message.Msg
		err, _ := m.ReadUnmarshal(n.Readers[from], readBuf)
		if err != nil {
			// maybe: TCP connection is closed or receives an ill-formed message
			return
		}
		n.RecvChan <- m
	}
}

func (n *NetTCP) SendHandler(to int) {
	defer n.Wg.Done()
	for {
		select {
		case <-n.Done:
			return
		case m := <-n.SendChan[to]:
			if err := message.WriteFlush(n.Writers[to], m); err != nil { // TCP connection closed (as RecvHandler)
				return
			}
		}
	}
}

func (n *NetTCP) PrintStatus() {
	fmt.Println("net layer id =", n.Id)
	for _, c := range n.SendConn {
		fmt.Println("\t ", (*c).LocalAddr(), "\tsend to  \t", (*c).RemoteAddr())
	}
	for _, c := range n.RecvConn {
		fmt.Println("\t ", (*c).LocalAddr(), "\trecv from\t", (*c).RemoteAddr())
	}
	fmt.Println()
}

func (n *NetTCP) Close() {
	for _, c := range n.SendConn {
		_ = (*c).Close()
	}
	for _, c := range n.RecvConn {
		_ = (*c).Close()
	}
	close(n.Done)
	_ = n.Listener.Close()
	n.Wg.Wait()
}
