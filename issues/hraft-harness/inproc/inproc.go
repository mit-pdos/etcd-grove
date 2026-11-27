// Package inproc (the hraft issues' copy of the verification fork's examples/inproc, at 02f88d5): the network of the verification fork's test, in one process: a raft.Transport for each server.
// Servers are numbered 1..n (address and ID strconv.Itoa(i)); in links, node 0 stands for the clients. Every
// request and response is a deep copy (as after serialization), delayed a little at random. The adversary can hold
// up a server's traffic, in both directions, for a while (Slow); cut a server off (Isolate); or cut the link from one
// node to another, one direction (Cut); or hold up a server's calls to the other servers only (SlowOut). A message on a cut link is lost: the call fails, as a call whose connection
// broke (a request delivered before the cut can lose its response). Cuts nest: a link is up again when every cut on
// it has ended. As upstream's NetworkTransport does, a heartbeat (an AppendEntries with a term and a leader and
// nothing else) goes to the server's heartbeat handler (SetHeartbeatHandler), run on the transport's side (here: the
// calling goroutine, standing for the receiving connection's goroutine), not through the server's RPC channel; and
// AppendEntriesPipeline offers a pipeline: its requests are sent in order, one connection's worth, and their
// responses come back in order. InstallSnapshot reads the snapshot in full on the caller's side and hands the
// receiving server a reader over a copy of its bytes (as a connection carries the request and then the stream).
package inproc

import (
	"errors"
	"io"
	"strconv"
	"sync"
	"time"

	"github.com/goose-lang/primitive"
	"github.com/hashicorp/raft"
)

var ErrCut = errors.New("inproc: link cut")
var ErrTimeout = errors.New("inproc: no response")
var ErrPipelineClosed = errors.New("inproc: pipeline closed")

// rpcTimeout: how long a caller waits for a response (upstream's InmemTransport: 500 ms)
const rpcTimeout = 500 * time.Millisecond

type Net struct {
	mu        *sync.Mutex
	n         int
	slowUntil []time.Time
	outUntil  []time.Time // per server: its calls to other servers are held up until then
	isolated  []int       // per server: the cuts of all its links in progress
	links     [][]int     // links[a][b]: the cuts of the link from node a to node b in progress (node 0: the clients)
	consumers []chan raft.RPC
	hbFns     []func(rpc raft.RPC) // per server: its heartbeat handler (nil until set)
}

func NewNet(n int) *Net {
	links := make([][]int, n+1)
	cons := make([]chan raft.RPC, n+1)
	for i := 0; i <= n; i++ {
		links[i] = make([]int, n+1)
		cons[i] = make(chan raft.RPC, 16)
	}
	return &Net{mu: new(sync.Mutex), n: n, slowUntil: make([]time.Time, n+1), outUntil: make([]time.Time, n+1), isolated: make([]int, n+1),
		links: links, consumers: cons, hbFns: make([]func(rpc raft.RPC), n+1)}
}

func Addr(i int) raft.ServerAddress {
	return raft.ServerAddress(strconv.Itoa(i))
}

// Isolate: start (on) or end a cut of every link of server i
func (nw *Net) Isolate(i int, on bool) {
	nw.mu.Lock()
	if on {
		nw.isolated[i]++
	} else {
		nw.isolated[i]--
	}
	nw.mu.Unlock()
}

// Cut: start (on) or end a cut of the link from node a to node b (0 for the clients)
func (nw *Net) Cut(a int, b int, on bool) {
	nw.mu.Lock()
	if on {
		nw.links[a][b]++
	} else {
		nw.links[a][b]--
	}
	nw.mu.Unlock()
}

// Slow: hold up server i's traffic for d
func (nw *Net) Slow(i int, d time.Duration) {
	nw.mu.Lock()
	nw.slowUntil[i] = time.Now().Add(d)
	nw.mu.Unlock()
}

// SlowOut: hold up server i's calls to the other servers for d (its other traffic flows)
func (nw *Net) SlowOut(i int, d time.Duration) {
	nw.mu.Lock()
	nw.outUntil[i] = time.Now().Add(d)
	nw.mu.Unlock()
}

// Lost: a message from a to b is lost
func (nw *Net) Lost(a int, b int) bool {
	if a == b {
		return false
	}
	nw.mu.Lock()
	c := nw.isolated[a] > 0 || nw.isolated[b] > 0 || nw.links[a][b] > 0
	nw.mu.Unlock()
	return c
}

// Delay: a message from a to b is held up while either is slow (or a's calls to servers are, when both are
// servers), then up to 2 ms more
func (nw *Net) Delay(a int, b int) {
	nw.mu.Lock()
	until := nw.slowUntil[a]
	if nw.slowUntil[b].After(until) {
		until = nw.slowUntil[b]
	}
	if a > 0 && b > 0 && nw.outUntil[a].After(until) {
		until = nw.outUntil[a]
	}
	nw.mu.Unlock()
	if d := time.Until(until); d > 0 {
		time.Sleep(d)
	}
	time.Sleep(time.Duration(primitive.RandomUint64()%2000) * time.Microsecond)
}

func index(a raft.ServerAddress) int {
	i, err := strconv.Atoi(string(a))
	if err != nil {
		panic("inproc: bad address")
	}
	return i
}

func copyBytes(b []byte) []byte {
	if b == nil {
		return nil
	}
	c := make([]byte, len(b))
	copy(c, b)
	return c
}

func copyHeader(h raft.RPCHeader) raft.RPCHeader {
	return raft.RPCHeader{ProtocolVersion: h.ProtocolVersion, ID: copyBytes(h.ID), Addr: copyBytes(h.Addr)}
}

func copyLog(l *raft.Log) *raft.Log {
	return &raft.Log{Index: l.Index, Term: l.Term, Type: l.Type, Data: copyBytes(l.Data),
		Extensions: copyBytes(l.Extensions), AppendedAt: l.AppendedAt}
}

// copyMsg: a deep copy of a request or response
func copyMsg(m interface{}) interface{} {
	switch x := m.(type) {
	case *raft.AppendEntriesRequest:
		var es []*raft.Log
		for _, e := range x.Entries {
			es = append(es, copyLog(e))
		}
		return &raft.AppendEntriesRequest{RPCHeader: copyHeader(x.RPCHeader), Term: x.Term, Leader: copyBytes(x.Leader),
			PrevLogEntry: x.PrevLogEntry, PrevLogTerm: x.PrevLogTerm, Entries: es, LeaderCommitIndex: x.LeaderCommitIndex}
	case *raft.AppendEntriesResponse:
		return &raft.AppendEntriesResponse{RPCHeader: copyHeader(x.RPCHeader), Term: x.Term, LastLog: x.LastLog,
			Success: x.Success, NoRetryBackoff: x.NoRetryBackoff}
	case *raft.RequestVoteRequest:
		return &raft.RequestVoteRequest{RPCHeader: copyHeader(x.RPCHeader), Term: x.Term, Candidate: copyBytes(x.Candidate),
			LastLogIndex: x.LastLogIndex, LastLogTerm: x.LastLogTerm, LeadershipTransfer: x.LeadershipTransfer}
	case *raft.RequestVoteResponse:
		return &raft.RequestVoteResponse{RPCHeader: copyHeader(x.RPCHeader), Term: x.Term, Peers: copyBytes(x.Peers),
			Granted: x.Granted}
	case *raft.RequestPreVoteRequest:
		return &raft.RequestPreVoteRequest{RPCHeader: copyHeader(x.RPCHeader), Term: x.Term, LastLogIndex: x.LastLogIndex,
			LastLogTerm: x.LastLogTerm}
	case *raft.RequestPreVoteResponse:
		return &raft.RequestPreVoteResponse{RPCHeader: copyHeader(x.RPCHeader), Term: x.Term, Granted: x.Granted}
	case *raft.InstallSnapshotRequest:
		return &raft.InstallSnapshotRequest{RPCHeader: copyHeader(x.RPCHeader), SnapshotVersion: x.SnapshotVersion,
			Term: x.Term, Leader: copyBytes(x.Leader), LastLogIndex: x.LastLogIndex, LastLogTerm: x.LastLogTerm,
			Peers: copyBytes(x.Peers), Configuration: copyBytes(x.Configuration), ConfigurationIndex: x.ConfigurationIndex,
			Size: x.Size}
	case *raft.InstallSnapshotResponse:
		return &raft.InstallSnapshotResponse{RPCHeader: copyHeader(x.RPCHeader), Term: x.Term, Success: x.Success}
	case *raft.TimeoutNowRequest:
		return &raft.TimeoutNowRequest{RPCHeader: copyHeader(x.RPCHeader)}
	case *raft.TimeoutNowResponse:
		return &raft.TimeoutNowResponse{RPCHeader: copyHeader(x.RPCHeader)}
	}
	panic("inproc: unknown message")
}

// Transport: server i's transport
type Transport struct {
	nw *Net
	i  int
}

func (nw *Net) Transport(i int) *Transport {
	return &Transport{nw: nw, i: i}
}

// call: send a copy of req to server j's consumer and wait for its response (a copy), unless the request or the
// response is lost or no response comes within rpcTimeout
func (t *Transport) call(j int, req interface{}) (interface{}, error) {
	return t.callWith(j, req, nil)
}

// callWith: call, with data as the request's stream (InstallSnapshot's; nil for every other request)
func (t *Transport) callWith(j int, req interface{}, data io.Reader) (interface{}, error) {
	nw := t.nw
	nw.Delay(t.i, j)
	if nw.Lost(t.i, j) {
		return nil, ErrCut
	}
	respCh := make(chan raft.RPCResponse, 1)
	timeout := time.After(rpcTimeout)
	if fn := nw.heartbeatFn(j, req); fn != nil {
		// the heartbeat fast path: the handler runs on the receiving transport's side, not in j's main loop
		fn(raft.RPC{Command: copyMsg(req), RespChan: respCh})
	} else {
		select {
		case nw.consumers[j] <- raft.RPC{Command: copyMsg(req), Reader: data, RespChan: respCh}:
		case <-timeout:
			return nil, ErrTimeout
		}
	}
	var r raft.RPCResponse
	select {
	case r = <-respCh:
	case <-timeout:
		return nil, ErrTimeout
	}
	nw.Delay(j, t.i)
	if nw.Lost(j, t.i) {
		return nil, ErrCut
	}
	if r.Error != nil {
		return nil, r.Error
	}
	return copyMsg(r.Response), nil
}

func (t *Transport) Consumer() <-chan raft.RPC {
	return t.nw.consumers[t.i]
}

func (t *Transport) LocalAddr() raft.ServerAddress {
	return Addr(t.i)
}

// heartbeatFn: server j's heartbeat handler if req is a heartbeat and j has one (upstream's NetworkTransport: an
// AppendEntries with a term and a leader, no previous entry, no entries and no commit index), else nil
func (nw *Net) heartbeatFn(j int, req interface{}) func(rpc raft.RPC) {
	a, ok := req.(*raft.AppendEntriesRequest)
	if !ok {
		return nil
	}
	leader := a.RPCHeader.Addr
	if len(leader) == 0 {
		leader = a.Leader
	}
	if a.Term == 0 || len(leader) == 0 || a.PrevLogEntry != 0 || a.PrevLogTerm != 0 || len(a.Entries) != 0 ||
		a.LeaderCommitIndex != 0 {
		return nil
	}
	nw.mu.Lock()
	defer nw.mu.Unlock()
	return nw.hbFns[j]
}

// appendFuture: one pipelined AppendEntries
type appendFuture struct {
	start time.Time
	req   *raft.AppendEntriesRequest
	resp  *raft.AppendEntriesResponse
	err   error
	done  chan struct{}
}

func (f *appendFuture) Error() error {
	<-f.done
	return f.err
}

func (f *appendFuture) Start() time.Time {
	return f.start
}

func (f *appendFuture) Request() *raft.AppendEntriesRequest {
	return f.req
}

func (f *appendFuture) Response() *raft.AppendEntriesResponse {
	return f.resp
}

// pipeline: a stream of AppendEntries to one server, sent in order, their responses delivered in order
type pipeline struct {
	t        *Transport
	j        int
	queue    chan *appendFuture
	consumer chan raft.AppendFuture
	mu       *sync.Mutex
	closed   bool
	closeCh  chan struct{}
}

// maxPipelineInflight: as upstream's NetworkTransport (rpcMaxPipeline)
const maxPipelineInflight = 128

func (t *Transport) AppendEntriesPipeline(id raft.ServerID, target raft.ServerAddress) (raft.AppendPipeline, error) {
	p := &pipeline{t: t, j: index(target), queue: make(chan *appendFuture, maxPipelineInflight),
		consumer: make(chan raft.AppendFuture, maxPipelineInflight), mu: new(sync.Mutex), closeCh: make(chan struct{})}
	go p.run()
	return p, nil
}

// run: send the queued requests one after another; each response (or failure) completes its future, in order
func (p *pipeline) run() {
	for {
		var f *appendFuture
		select {
		case f = <-p.queue:
		case <-p.closeCh:
			return
		}
		r, err := p.t.call(p.j, f.req)
		if err != nil {
			f.err = err
		} else {
			*f.resp = *r.(*raft.AppendEntriesResponse)
		}
		close(f.done)
		select {
		case p.consumer <- f:
		case <-p.closeCh:
			return
		}
	}
}

func (p *pipeline) AppendEntries(args *raft.AppendEntriesRequest, resp *raft.AppendEntriesResponse) (raft.AppendFuture, error) {
	p.mu.Lock()
	closed := p.closed
	p.mu.Unlock()
	if closed {
		return nil, ErrPipelineClosed
	}
	f := &appendFuture{start: time.Now(), req: args, resp: resp, done: make(chan struct{})}
	select {
	case p.queue <- f:
	case <-p.closeCh:
		return nil, ErrPipelineClosed
	}
	return f, nil
}

func (p *pipeline) Consumer() <-chan raft.AppendFuture {
	return p.consumer
}

func (p *pipeline) Close() error {
	p.mu.Lock()
	defer p.mu.Unlock()
	if !p.closed {
		p.closed = true
		close(p.closeCh)
	}
	return nil
}

func (t *Transport) AppendEntries(id raft.ServerID, target raft.ServerAddress, args *raft.AppendEntriesRequest, resp *raft.AppendEntriesResponse) error {
	r, err := t.call(index(target), args)
	if err != nil {
		return err
	}
	*resp = *r.(*raft.AppendEntriesResponse)
	return nil
}

func (t *Transport) RequestVote(id raft.ServerID, target raft.ServerAddress, args *raft.RequestVoteRequest, resp *raft.RequestVoteResponse) error {
	r, err := t.call(index(target), args)
	if err != nil {
		return err
	}
	*resp = *r.(*raft.RequestVoteResponse)
	return nil
}

func (t *Transport) RequestPreVote(id raft.ServerID, target raft.ServerAddress, args *raft.RequestPreVoteRequest, resp *raft.RequestPreVoteResponse) error {
	r, err := t.call(index(target), args)
	if err != nil {
		return err
	}
	*resp = *r.(*raft.RequestPreVoteResponse)
	return nil
}

// InstallSnapshot: the snapshot's bytes are read from data in full, then the request goes to the target with a
// reader over a copy of them
func (t *Transport) InstallSnapshot(id raft.ServerID, target raft.ServerAddress, args *raft.InstallSnapshotRequest, resp *raft.InstallSnapshotResponse, data io.Reader) error {
	b, err := ReadAll(data)
	if err != nil {
		return err
	}
	r, err := t.callWith(index(target), args, NewReader(b))
	if err != nil {
		return err
	}
	*resp = *r.(*raft.InstallSnapshotResponse)
	return nil
}

// Reader: an io.Reader over a byte slice (each call copies up to len(p) bytes; io.EOF at the end)
type Reader struct {
	b   []byte
	off int
}

// NewReader: a Reader over a copy of b
func NewReader(b []byte) *Reader {
	return &Reader{b: copyBytes(b)}
}

func (r *Reader) Read(p []byte) (int, error) {
	if r.off >= len(r.b) {
		return 0, io.EOF
	}
	n := copy(p, r.b[r.off:])
	r.off += n
	return n, nil
}

// Close: nothing to release (a Reader is also an io.ReadCloser)
func (r *Reader) Close() error {
	return nil
}

// ReadAll: every byte of r until io.EOF (read 512 bytes at a time), or r's other error
func ReadAll(r io.Reader) ([]byte, error) {
	var out []byte
	buf := make([]byte, 512)
	for {
		n, err := r.Read(buf)
		out = append(out, buf[:n]...)
		if err == io.EOF {
			return out, nil
		}
		if err != nil {
			return out, err
		}
	}
}

func (t *Transport) TimeoutNow(id raft.ServerID, target raft.ServerAddress, args *raft.TimeoutNowRequest, resp *raft.TimeoutNowResponse) error {
	r, err := t.call(index(target), args)
	if err != nil {
		return err
	}
	*resp = *r.(*raft.TimeoutNowResponse)
	return nil
}

func (t *Transport) EncodePeer(id raft.ServerID, addr raft.ServerAddress) []byte {
	return []byte(addr)
}

func (t *Transport) DecodePeer(buf []byte) raft.ServerAddress {
	return raft.ServerAddress(buf)
}

// SetHeartbeatHandler: heartbeats to this server go to cb, on the transport's side (as upstream's NetworkTransport)
func (t *Transport) SetHeartbeatHandler(cb func(rpc raft.RPC)) {
	t.nw.mu.Lock()
	t.nw.hbFns[t.i] = cb
	t.nw.mu.Unlock()
}
