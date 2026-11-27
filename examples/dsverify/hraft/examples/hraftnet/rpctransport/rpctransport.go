// Package rpctransport is a raft transport over net/rpc (raft.Transport, raft.WithPreVote), the
// hraft kit's (examples/hraftnet): a server's raft RPCs go to the other servers' RaftRPC
// receivers, on one *rpc.Client per peer (Conn). A raft message crosses the network in a flat wire struct of this file (rpcgen's
// codec does not take raft's embedded RPCHeader, its []*Log or a time.Time): the caller converts
// its request into one and the answer back into raft's response, the receiver the other way round.
// So a message raft receives is a fresh copy, and a late answer (one that comes after the caller
// gave up) is decoded into a wire struct nobody reads again, never into raft's memory. An error of
// the receiving raft travels in the answer (Failed, Err); the RPC methods always return nil.
//
// As upstream's NetworkTransport does: a heartbeat (an AppendEntries with a term and a leader and
// nothing else) goes to the handler raft set (SetHeartbeatHandler), not through raft's RPC
// channel (upstream runs it on the receiving connection's goroutine; here it runs on a goroutine of
// its own while the receiving one waits for its answer); AppendEntriesPipeline is a pipeline whose requests
// are sent one after another and whose answers come back in order; InstallSnapshot carries the
// snapshot's bytes in the request, and the receiving raft reads them from a reader over a copy.
// The transport maps a peer's raft address to its network address (New's peers): a raft address
// need not be a network address. A request whose encoding may be longer than MaxRequest (the
// net/rpc model's frame bound; *ReqBound) is refused with an error before it is sent, which raft
// retries as any failed call: a liveness cost only, which no request of the kit comes near.
package rpctransport

import (
	"errors"
	"io"
	"net"
	"net/rpc"
	"sync"
	"time"

	"github.com/hashicorp/raft"
	"github.com/hashicorp/raft/examples/snapstore"
)

// Header is raft.RPCHeader on the wire.
type Header struct {
	ProtocolVersion raft.ProtocolVersion
	ID              []byte
	Addr            []byte
}

// Entry is a raft.Log on the wire (its AppendedAt is not sent: raft never reads a received one).
type Entry struct {
	Index      uint64
	Term       uint64
	Type       raft.LogType
	Data       []byte
	Extensions []byte
}

// AppendReq is a raft.AppendEntriesRequest on the wire.
type AppendReq struct {
	Hdr               Header
	Term              uint64
	Leader            []byte
	PrevLogEntry      uint64
	PrevLogTerm       uint64
	Entries           []Entry
	LeaderCommitIndex uint64
}

// AppendResp is a raft.AppendEntriesResponse on the wire, or the receiving raft's error (Failed,
// with its message Err).
type AppendResp struct {
	Failed         bool
	Err            string
	Hdr            Header
	Term           uint64
	LastLog        uint64
	Success        bool
	NoRetryBackoff bool
}

// VoteReq is a raft.RequestVoteRequest on the wire.
type VoteReq struct {
	Hdr                Header
	Term               uint64
	Candidate          []byte
	LastLogIndex       uint64
	LastLogTerm        uint64
	LeadershipTransfer bool
}

// VoteResp is a raft.RequestVoteResponse on the wire, or an error.
type VoteResp struct {
	Failed  bool
	Err     string
	Hdr     Header
	Term    uint64
	Peers   []byte
	Granted bool
}

// PreVoteReq is a raft.RequestPreVoteRequest on the wire.
type PreVoteReq struct {
	Hdr          Header
	Term         uint64
	LastLogIndex uint64
	LastLogTerm  uint64
}

// PreVoteResp is a raft.RequestPreVoteResponse on the wire, or an error.
type PreVoteResp struct {
	Failed  bool
	Err     string
	Hdr     Header
	Term    uint64
	Granted bool
}

// SnapReq is a raft.InstallSnapshotRequest on the wire, with the snapshot's bytes (Data).
type SnapReq struct {
	Hdr                Header
	SnapshotVersion    raft.SnapshotVersion
	Term               uint64
	Leader             []byte
	LastLogIndex       uint64
	LastLogTerm        uint64
	Peers              []byte
	Configuration      []byte
	ConfigurationIndex uint64
	Size               int64
	Data               []byte
}

// SnapResp is a raft.InstallSnapshotResponse on the wire, or an error.
type SnapResp struct {
	Failed  bool
	Err     string
	Hdr     Header
	Term    uint64
	Success bool
}

// TimeoutReq is a raft.TimeoutNowRequest on the wire.
type TimeoutReq struct {
	Hdr Header
}

// TimeoutResp is a raft.TimeoutNowResponse on the wire, or an error.
type TimeoutResp struct {
	Failed bool
	Err    string
	Hdr    Header
}

// --- the size check

// MaxRequest is the longest encoded request the transport sends: the net/rpc model has no
// behavior for a request frame longer than 1 GiB (models/net/rpc/codec.go's maxFrame: a client
// writing one is stuck), so a request whose wire-size bound exceeds it is refused (an error, which
// raft retries like any failed call: only liveness is lost; no request of the kit comes near it).
const MaxRequest uint64 = 1 << 30

// tooLarge is the error of a refused request.
const tooLarge = "rpctransport: request too large"

// BytesBound bounds the encoded length of a byte-slice field (rpcgen's encoding,
// models/net/rpc/rpcgen_core.py: a sent flag, the length, 8 bytes per byte), saturating above
// MaxRequest (so that the sums below do not overflow).
func BytesBound(b []byte) uint64 {
	n := uint64(len(b))
	if n > MaxRequest {
		return MaxRequest + 1
	}
	return 17 + 8*n
}

// hdrBound bounds the encoded length of a Header field (its flag, the struct's, the version's,
// both slices).
func hdrBound(h *Header) uint64 {
	return 16 + BytesBound(h.ID) + BytesBound(h.Addr)
}

// tagBound bounds the encoded length of a request's type tag and struct marker (the longest
// tag, rpctransport.TimeoutResp's, has 68 bytes, after its 8-byte length).
const tagBound uint64 = 128

// AppendReqBound is a conservative bound on the length of the encoding of a (rpcgen's codec):
// at least it (rpctransport_test.go's TestBounds, against the generated encoder).
func AppendReqBound(a *AppendReq) uint64 {
	n := tagBound + hdrBound(&a.Hdr) + BytesBound(a.Leader) + 64
	for _, e := range a.Entries {
		if n > MaxRequest {
			return n
		}
		n = n + 64 + BytesBound(e.Data) + BytesBound(e.Extensions)
	}
	return n
}

// VoteReqBound is a conservative bound on the length of the encoding of a (TestBounds).
func VoteReqBound(a *VoteReq) uint64 {
	return tagBound + hdrBound(&a.Hdr) + BytesBound(a.Candidate) + 64
}

// PreVoteReqBound is a conservative bound on the length of the encoding of a (TestBounds).
func PreVoteReqBound(a *PreVoteReq) uint64 {
	return tagBound + hdrBound(&a.Hdr) + 64
}

// SnapReqBound is a conservative bound on the length of the encoding of a (TestBounds).
func SnapReqBound(a *SnapReq) uint64 {
	return tagBound + hdrBound(&a.Hdr) + BytesBound(a.Leader) + BytesBound(a.Peers) +
		BytesBound(a.Configuration) + BytesBound(a.Data) + 128
}

// TimeoutReqBound is a conservative bound on the length of the encoding of a (TestBounds).
func TimeoutReqBound(a *TimeoutReq) uint64 {
	return tagBound + hdrBound(&a.Hdr)
}

// copyBytes is a fresh copy of b (nil for nil).
func copyBytes(b []byte) []byte {
	if b == nil {
		return nil
	}
	c := make([]byte, len(b))
	copy(c, b)
	return c
}

func toHeader(h raft.RPCHeader) Header {
	return Header{ProtocolVersion: h.ProtocolVersion, ID: copyBytes(h.ID), Addr: copyBytes(h.Addr)}
}

func fromHeader(h Header) raft.RPCHeader {
	return raft.RPCHeader{ProtocolVersion: h.ProtocolVersion, ID: copyBytes(h.ID), Addr: copyBytes(h.Addr)}
}

func toAppendReq(a *raft.AppendEntriesRequest) *AppendReq {
	var es []Entry
	for _, l := range a.Entries {
		es = append(es, Entry{Index: l.Index, Term: l.Term, Type: l.Type, Data: copyBytes(l.Data),
			Extensions: copyBytes(l.Extensions)})
	}
	return &AppendReq{Hdr: toHeader(a.RPCHeader), Term: a.Term, Leader: copyBytes(a.Leader),
		PrevLogEntry: a.PrevLogEntry, PrevLogTerm: a.PrevLogTerm, Entries: es,
		LeaderCommitIndex: a.LeaderCommitIndex}
}

func fromAppendReq(a *AppendReq) *raft.AppendEntriesRequest {
	var es []*raft.Log
	for _, e := range a.Entries {
		es = append(es, &raft.Log{Index: e.Index, Term: e.Term, Type: e.Type, Data: copyBytes(e.Data),
			Extensions: copyBytes(e.Extensions)})
	}
	return &raft.AppendEntriesRequest{RPCHeader: fromHeader(a.Hdr), Term: a.Term, Leader: copyBytes(a.Leader),
		PrevLogEntry: a.PrevLogEntry, PrevLogTerm: a.PrevLogTerm, Entries: es,
		LeaderCommitIndex: a.LeaderCommitIndex}
}

func toAppendResp(r *raft.AppendEntriesResponse) AppendResp {
	return AppendResp{Hdr: toHeader(r.RPCHeader), Term: r.Term, LastLog: r.LastLog, Success: r.Success,
		NoRetryBackoff: r.NoRetryBackoff}
}

func fromAppendResp(r *AppendResp) raft.AppendEntriesResponse {
	return raft.AppendEntriesResponse{RPCHeader: fromHeader(r.Hdr), Term: r.Term, LastLog: r.LastLog,
		Success: r.Success, NoRetryBackoff: r.NoRetryBackoff}
}

func toVoteReq(a *raft.RequestVoteRequest) *VoteReq {
	return &VoteReq{Hdr: toHeader(a.RPCHeader), Term: a.Term, Candidate: copyBytes(a.Candidate),
		LastLogIndex: a.LastLogIndex, LastLogTerm: a.LastLogTerm, LeadershipTransfer: a.LeadershipTransfer}
}

func fromVoteReq(a *VoteReq) *raft.RequestVoteRequest {
	return &raft.RequestVoteRequest{RPCHeader: fromHeader(a.Hdr), Term: a.Term, Candidate: copyBytes(a.Candidate),
		LastLogIndex: a.LastLogIndex, LastLogTerm: a.LastLogTerm, LeadershipTransfer: a.LeadershipTransfer}
}

func toVoteResp(r *raft.RequestVoteResponse) VoteResp {
	return VoteResp{Hdr: toHeader(r.RPCHeader), Term: r.Term, Peers: copyBytes(r.Peers), Granted: r.Granted}
}

func fromVoteResp(r *VoteResp) raft.RequestVoteResponse {
	return raft.RequestVoteResponse{RPCHeader: fromHeader(r.Hdr), Term: r.Term, Peers: copyBytes(r.Peers),
		Granted: r.Granted}
}

func toPreVoteReq(a *raft.RequestPreVoteRequest) *PreVoteReq {
	return &PreVoteReq{Hdr: toHeader(a.RPCHeader), Term: a.Term, LastLogIndex: a.LastLogIndex,
		LastLogTerm: a.LastLogTerm}
}

func fromPreVoteReq(a *PreVoteReq) *raft.RequestPreVoteRequest {
	return &raft.RequestPreVoteRequest{RPCHeader: fromHeader(a.Hdr), Term: a.Term, LastLogIndex: a.LastLogIndex,
		LastLogTerm: a.LastLogTerm}
}

func toPreVoteResp(r *raft.RequestPreVoteResponse) PreVoteResp {
	return PreVoteResp{Hdr: toHeader(r.RPCHeader), Term: r.Term, Granted: r.Granted}
}

func fromPreVoteResp(r *PreVoteResp) raft.RequestPreVoteResponse {
	return raft.RequestPreVoteResponse{RPCHeader: fromHeader(r.Hdr), Term: r.Term, Granted: r.Granted}
}

func toSnapReq(a *raft.InstallSnapshotRequest, data []byte) *SnapReq {
	return &SnapReq{Hdr: toHeader(a.RPCHeader), SnapshotVersion: a.SnapshotVersion, Term: a.Term,
		Leader: copyBytes(a.Leader), LastLogIndex: a.LastLogIndex, LastLogTerm: a.LastLogTerm,
		Peers: copyBytes(a.Peers), Configuration: copyBytes(a.Configuration),
		ConfigurationIndex: a.ConfigurationIndex, Size: a.Size, Data: data}
}

func fromSnapReq(a *SnapReq) *raft.InstallSnapshotRequest {
	return &raft.InstallSnapshotRequest{RPCHeader: fromHeader(a.Hdr), SnapshotVersion: a.SnapshotVersion,
		Term: a.Term, Leader: copyBytes(a.Leader), LastLogIndex: a.LastLogIndex, LastLogTerm: a.LastLogTerm,
		Peers: copyBytes(a.Peers), Configuration: copyBytes(a.Configuration),
		ConfigurationIndex: a.ConfigurationIndex, Size: a.Size}
}

func toSnapResp(r *raft.InstallSnapshotResponse) SnapResp {
	return SnapResp{Hdr: toHeader(r.RPCHeader), Term: r.Term, Success: r.Success}
}

func fromSnapResp(r *SnapResp) raft.InstallSnapshotResponse {
	return raft.InstallSnapshotResponse{RPCHeader: fromHeader(r.Hdr), Term: r.Term, Success: r.Success}
}

// --- connections

// Outcomes of a call (Conn.Call).
const (
	CallOK      uint64 = 0 // answered
	CallNotSent uint64 = 1 // no connection: the request was not sent
	CallFailed  uint64 = 2 // no answer (the request may have been delivered)
)

// Conn is the connection to one net/rpc server: a client dialed when needed (net.DialTimeout,
// then rpc.NewClient: rpc.Dial with a timeout) and dropped after an error, so that the next call
// dials again.
type Conn struct {
	mu   sync.Mutex
	addr string
	c    *rpc.Client
}

// NewConn is a connection to the net/rpc server at addr (dialed at its first call).
func NewConn(addr string) *Conn {
	return &Conn{addr: addr}
}

// get is the connection's client, dialed (within d) if it has none; nil if the dial fails.
func (p *Conn) get(d time.Duration) *rpc.Client {
	p.mu.Lock()
	if p.c == nil {
		nc, err := net.DialTimeout("tcp", p.addr, d)
		if err == nil {
			p.c = rpc.NewClient(nc)
		}
	}
	c := p.c
	p.mu.Unlock()
	return c
}

// drop closes c and forgets it, if it is still the connection's client.
func (p *Conn) drop(c *rpc.Client) {
	p.mu.Lock()
	if p.c == c {
		p.c = nil
	}
	p.mu.Unlock()
	c.Close()
}

// Call calls method with args, its answer decoded into reply, waiting at most d for the dial and
// at most d for the answer. A failed or late call drops the connection; a late answer goes into
// reply, which the caller must not read after CallFailed.
func (p *Conn) Call(method string, args any, reply any, d time.Duration) uint64 {
	c := p.get(d)
	if c == nil {
		return CallNotSent
	}
	call := c.Go(method, args, reply, make(chan *rpc.Call, 1))
	select {
	case done := <-call.Done:
		// done is call (net/rpc sends the call on its Done), read as rpc.Client.Call does
		if done.Error != nil {
			p.drop(c)
			return CallFailed
		}
		return CallOK
	case <-time.After(d):
		p.drop(c)
		return CallFailed
	}
}

// --- the transport

// Transport is a server's raft transport.
type Transport struct {
	local    raft.ServerAddress
	timeout  time.Duration
	consumer chan raft.RPC
	peers    map[raft.ServerAddress]*Conn // by raft address; never changed
	mu       sync.Mutex
	hb       func(rpc raft.RPC) // the heartbeat handler (nil until raft sets it)
}

// New is the transport of the server at raft address local, whose peers are at the network
// addresses peers[a] (a peer's raft address a), each RPC waiting at most timeout for its answer.
func New(local raft.ServerAddress, peers map[raft.ServerAddress]string, timeout time.Duration) *Transport {
	conns := make(map[raft.ServerAddress]*Conn)
	for a, addr := range peers {
		conns[a] = NewConn(addr)
	}
	return &Transport{local: local, timeout: timeout, consumer: make(chan raft.RPC), peers: conns}
}

// Receiver is the transport's net/rpc receiver, which its server registers (as "RaftRPC").
func (t *Transport) Receiver() *RaftRPC {
	return &RaftRPC{t: t}
}

// send sends req to target's RaftRPC.method, its answer into reply; an error if target is not a
// peer or no answer came.
func (t *Transport) send(target raft.ServerAddress, method string, req any, reply any) error {
	p, ok := t.peers[target]
	if !ok {
		return errors.New("rpctransport: unknown peer")
	}
	if p.Call("RaftRPC."+method, req, reply, t.timeout) != CallOK {
		return errors.New("rpctransport: no answer")
	}
	return nil
}

func (t *Transport) Consumer() <-chan raft.RPC {
	return t.consumer
}

func (t *Transport) LocalAddr() raft.ServerAddress {
	return t.local
}

func (t *Transport) EncodePeer(id raft.ServerID, addr raft.ServerAddress) []byte {
	return []byte(addr)
}

func (t *Transport) DecodePeer(buf []byte) raft.ServerAddress {
	return raft.ServerAddress(buf)
}

// SetHeartbeatHandler sets the handler heartbeats go to (deliver).
func (t *Transport) SetHeartbeatHandler(cb func(rpc raft.RPC)) {
	t.mu.Lock()
	t.hb = cb
	t.mu.Unlock()
}

func (t *Transport) AppendEntries(id raft.ServerID, target raft.ServerAddress, args *raft.AppendEntriesRequest, resp *raft.AppendEntriesResponse) error {
	w := toAppendReq(args)
	if AppendReqBound(w) > MaxRequest {
		return errors.New(tooLarge)
	}
	reply := new(AppendResp)
	if err := t.send(target, "AppendEntries", w, reply); err != nil {
		return err
	}
	if reply.Failed {
		return errors.New(reply.Err)
	}
	*resp = fromAppendResp(reply)
	return nil
}

func (t *Transport) RequestVote(id raft.ServerID, target raft.ServerAddress, args *raft.RequestVoteRequest, resp *raft.RequestVoteResponse) error {
	w := toVoteReq(args)
	if VoteReqBound(w) > MaxRequest {
		return errors.New(tooLarge)
	}
	reply := new(VoteResp)
	if err := t.send(target, "RequestVote", w, reply); err != nil {
		return err
	}
	if reply.Failed {
		return errors.New(reply.Err)
	}
	*resp = fromVoteResp(reply)
	return nil
}

func (t *Transport) RequestPreVote(id raft.ServerID, target raft.ServerAddress, args *raft.RequestPreVoteRequest, resp *raft.RequestPreVoteResponse) error {
	w := toPreVoteReq(args)
	if PreVoteReqBound(w) > MaxRequest {
		return errors.New(tooLarge)
	}
	reply := new(PreVoteResp)
	if err := t.send(target, "RequestPreVote", w, reply); err != nil {
		return err
	}
	if reply.Failed {
		return errors.New(reply.Err)
	}
	*resp = fromPreVoteResp(reply)
	return nil
}

// InstallSnapshot reads the snapshot from data in full and sends it in the request.
func (t *Transport) InstallSnapshot(id raft.ServerID, target raft.ServerAddress, args *raft.InstallSnapshotRequest, resp *raft.InstallSnapshotResponse, data io.Reader) error {
	b, err := snapstore.ReadAll(data)
	if err != nil {
		return err
	}
	w := toSnapReq(args, b)
	if SnapReqBound(w) > MaxRequest {
		return errors.New(tooLarge)
	}
	reply := new(SnapResp)
	if err := t.send(target, "InstallSnapshot", w, reply); err != nil {
		return err
	}
	if reply.Failed {
		return errors.New(reply.Err)
	}
	*resp = fromSnapResp(reply)
	return nil
}

func (t *Transport) TimeoutNow(id raft.ServerID, target raft.ServerAddress, args *raft.TimeoutNowRequest, resp *raft.TimeoutNowResponse) error {
	w := &TimeoutReq{Hdr: toHeader(args.RPCHeader)}
	if TimeoutReqBound(w) > MaxRequest {
		return errors.New(tooLarge)
	}
	reply := new(TimeoutResp)
	if err := t.send(target, "TimeoutNow", w, reply); err != nil {
		return err
	}
	if reply.Failed {
		return errors.New(reply.Err)
	}
	*resp = raft.TimeoutNowResponse{RPCHeader: fromHeader(reply.Hdr)}
	return nil
}

// --- the pipeline (examples/inproc's, over AppendEntries)

// appendFuture is one pipelined AppendEntries.
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

// pipeline is a stream of AppendEntries to one server, sent in order, their outcomes delivered in
// order.
type pipeline struct {
	t        *Transport
	target   raft.ServerAddress
	queue    chan *appendFuture
	consumer chan raft.AppendFuture
	mu       sync.Mutex
	closed   bool
	closeCh  chan struct{}
}

// maxPipelineInflight is upstream's NetworkTransport's (rpcMaxPipeline).
const maxPipelineInflight = 128

func (t *Transport) AppendEntriesPipeline(id raft.ServerID, target raft.ServerAddress) (raft.AppendPipeline, error) {
	p := &pipeline{t: t, target: target, queue: make(chan *appendFuture, maxPipelineInflight),
		consumer: make(chan raft.AppendFuture, maxPipelineInflight), closeCh: make(chan struct{})}
	go p.run()
	return p, nil
}

// run sends the queued requests one after another; each answer (or failure) completes its future,
// in order. (The explicit conversion at the consumer's send: mit-pdos/perennial#713.)
func (p *pipeline) run() {
	for {
		var f *appendFuture
		select {
		case f = <-p.queue:
		case <-p.closeCh:
			return
		}
		f.err = p.t.AppendEntries("", p.target, f.req, f.resp)
		close(f.done)
		select {
		case p.consumer <- raft.AppendFuture(f):
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
		return nil, raft.ErrPipelineShutdown
	}
	f := &appendFuture{start: time.Now(), req: args, resp: resp, done: make(chan struct{})}
	select {
	case p.queue <- f:
	case <-p.closeCh:
		return nil, raft.ErrPipelineShutdown
	}
	return f, nil
}

func (p *pipeline) Consumer() <-chan raft.AppendFuture {
	return p.consumer
}

func (p *pipeline) Close() error {
	p.mu.Lock()
	if !p.closed {
		p.closed = true
		close(p.closeCh)
	}
	p.mu.Unlock()
	return nil
}

// --- the receiving side

// RaftRPC is the net/rpc receiver of a server's raft RPCs: each hands raft a fresh request and
// answers with raft's response (or its error).
type RaftRPC struct {
	t *Transport
}

// isHeartbeat says whether a is a heartbeat (upstream NetworkTransport's test: a term and a
// leader, no previous entry, no entries, no commit index).
func isHeartbeat(a *raft.AppendEntriesRequest) bool {
	leader := a.RPCHeader.Addr
	if len(leader) == 0 {
		leader = a.Leader
	}
	return a.Term != 0 && len(leader) != 0 && a.PrevLogEntry == 0 && a.PrevLogTerm == 0 &&
		len(a.Entries) == 0 && a.LeaderCommitIndex == 0
}

// deliver hands raft cmd (with data, InstallSnapshot's reader; nil otherwise): a heartbeat (hb)
// to the heartbeat handler if raft set one, on a goroutine of its own, anything else to the
// consumer; then it waits for raft's response. (Upstream's NetworkTransport runs the handler on
// the connection's goroutine; here the RPC's goroutine waits on respCh while it runs, which is the
// same behavior: the fresh goroutine is what gives the handler a thread of its own in the proof,
// since net/rpc's method goroutine lends none.)
func (t *Transport) deliver(cmd any, data io.Reader, hb bool) (any, error) {
	respCh := make(chan raft.RPCResponse, 1)
	r := raft.RPC{Command: cmd, Reader: data, RespChan: respCh}
	var fn func(rpc raft.RPC)
	if hb {
		t.mu.Lock()
		fn = t.hb
		t.mu.Unlock()
	}
	if fn != nil {
		go fn(r)
	} else {
		t.consumer <- r
	}
	resp := <-respCh
	return resp.Response, resp.Error
}

// unexpected is the error message of a response of another type than the request's.
const unexpected = "rpctransport: unexpected response"

func (s *RaftRPC) AppendEntries(args *AppendReq, reply *AppendResp) error {
	req := fromAppendReq(args)
	resp, err := s.t.deliver(req, nil, isHeartbeat(req))
	if err != nil {
		reply.Failed = true
		reply.Err = err.Error()
		return nil
	}
	r, ok := resp.(*raft.AppendEntriesResponse)
	if !ok {
		reply.Failed = true
		reply.Err = unexpected
		return nil
	}
	*reply = toAppendResp(r)
	return nil
}

func (s *RaftRPC) RequestVote(args *VoteReq, reply *VoteResp) error {
	resp, err := s.t.deliver(fromVoteReq(args), nil, false)
	if err != nil {
		reply.Failed = true
		reply.Err = err.Error()
		return nil
	}
	r, ok := resp.(*raft.RequestVoteResponse)
	if !ok {
		reply.Failed = true
		reply.Err = unexpected
		return nil
	}
	*reply = toVoteResp(r)
	return nil
}

func (s *RaftRPC) RequestPreVote(args *PreVoteReq, reply *PreVoteResp) error {
	resp, err := s.t.deliver(fromPreVoteReq(args), nil, false)
	if err != nil {
		reply.Failed = true
		reply.Err = err.Error()
		return nil
	}
	r, ok := resp.(*raft.RequestPreVoteResponse)
	if !ok {
		reply.Failed = true
		reply.Err = unexpected
		return nil
	}
	*reply = toPreVoteResp(r)
	return nil
}

// installFailed is the error message of a failed install: raft's InstallSnapshot error may be any
// error (io.Copy's, the sink's, the FSM's Restore's), whose Error() the receiver does not call; the
// sender only tests the error against nil.
const installFailed = "rpctransport: snapshot install failed"

func (s *RaftRPC) InstallSnapshot(args *SnapReq, reply *SnapResp) error {
	resp, err := s.t.deliver(fromSnapReq(args), snapstore.NewReader(args.Data), false)
	if err != nil {
		reply.Failed = true
		reply.Err = installFailed
		return nil
	}
	r, ok := resp.(*raft.InstallSnapshotResponse)
	if !ok {
		reply.Failed = true
		reply.Err = unexpected
		return nil
	}
	*reply = toSnapResp(r)
	return nil
}

func (s *RaftRPC) TimeoutNow(args *TimeoutReq, reply *TimeoutResp) error {
	resp, err := s.t.deliver(&raft.TimeoutNowRequest{RPCHeader: fromHeader(args.Hdr)}, nil, false)
	if err != nil {
		reply.Failed = true
		reply.Err = err.Error()
		return nil
	}
	r, ok := resp.(*raft.TimeoutNowResponse)
	if !ok {
		reply.Failed = true
		reply.Err = unexpected
		return nil
	}
	reply.Hdr = toHeader(r.RPCHeader)
	return nil
}
