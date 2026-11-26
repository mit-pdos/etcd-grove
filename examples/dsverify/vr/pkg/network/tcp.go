package network

import (
	"encoding/json"
	"errors"
	"io"
	"log/slog"
	"net"
	"sync"

	"github.com/tangledbytes/go-vsr/pkg/assert"
	"github.com/tangledbytes/go-vsr/pkg/events"
	"github.com/tangledbytes/go-vsr/pkg/ipv4port"
	"github.com/tangledbytes/go-vsr/pkg/queue"
)

// ErrNoConn is Send's error for the source address of an accepted connection that has ended.
var ErrNoConn = errors.New("network: no connection to the source address")

type TCP struct {
	ip ipv4port.IPv4Port

	conns map[string]net.Conn
	// srcs is the set of the keys of the accepted connections (their remote addresses):
	// Send never dials one of them.
	srcs map[string]bool

	queue *queue.Queue[events.NetworkEvent]
	mu    *sync.RWMutex
}

func NewTCP(hostname string) *TCP {
	ipv4port := ipv4port.IPv4Port{}
	err := ipv4port.FromHostPort(hostname)
	assert.Assert(err == nil, "err should be nil")

	return &TCP{
		ip:    ipv4port,
		conns: make(map[string]net.Conn),
		srcs:  make(map[string]bool),
		mu:    new(sync.RWMutex),
		queue: queue.New[events.NetworkEvent](),
	}
}

func (tcp *TCP) Run() error {
	listener, err := net.Listen("tcp4", tcp.ip.String())
	if err != nil {
		return err
	}

	slog.Debug("started listener", "addr", tcp.ip.String())

	return tcp.serve(listener)
}

// serve accepts connections on listener, forever.
func (tcp *TCP) serve(listener net.Listener) error {
	for {
		conn, err := listener.Accept()
		if err != nil {
			// On error Accept's Conn is nil (Go's net.Listener): nothing to use.
			slog.Debug("failed to accept a connection", "err", err)
			continue
		}

		// The connection's key and its events' source: its remote address, read once (in Go
		// a connection's address string is fixed).
		key := conn.RemoteAddr().String()
		slog.Debug("accepted a connection", "remote-addr", key)
		tcp.mu.Lock()
		tcp.conns[key] = conn
		tcp.srcs[key] = true
		tcp.mu.Unlock()

		go tcp.handleConn(conn, key, ipv4port.FromAddrString(key))
	}
}

func (tcp *TCP) Send(ipv4port ipv4port.IPv4Port, f func(io.Writer) error) error {
	slog.Debug("received request to send", "ipv4port", ipv4port.String())

	tcp.mu.RLock()
	conn, ok := tcp.conns[ipv4port.String()]
	accepted := tcp.srcs[ipv4port.String()]
	tcp.mu.RUnlock()
	if !ok {
		if accepted {
			// The source of an accepted connection that has ended: a peer's or client's
			// ephemeral port, where nothing listens (a dial there is refused).
			slog.Debug("no connection to an accepted source", "ipv4port", ipv4port.String())
			return ErrNoConn
		}

		var err error
		conn, err = net.Dial("tcp4", ipv4port.String())
		if err != nil {
			slog.Debug("failed to dial", "err", err)
			return err
		}

		tcp.mu.Lock()
		tcp.conns[ipv4port.String()] = conn
		tcp.mu.Unlock()

		// A dialed connection's key and its events' source: the dialed address (in Go its
		// RemoteAddr's string).
		go tcp.handleConn(conn, ipv4port.String(), ipv4port)
	}

	slog.Debug("attempting to send an event", "ipv4port", ipv4port.String())
	if err := f(conn); err != nil {
		slog.Debug("failed to send an event", "err", err)

		// The stream may now end in part of an event, and nothing written after it could be
		// framed: drop the connection (the next Send dials anew). This covers net.ErrClosed.
		tcp.mu.Lock()
		if err := conn.Close(); err != nil {
			slog.Debug("failed to close a connection after a failed send", "err", err)
		}
		if tcp.conns[ipv4port.String()] == conn {
			delete(tcp.conns, ipv4port.String())
		}
		tcp.mu.Unlock()

		return err
	}
	slog.Debug("sent an event", "ipv4port", ipv4port.String())

	return nil
}

func (tcp *TCP) Recv() (events.NetworkEvent, bool) {
	return tcp.queue.Pop()
}

// handleConn reads conn's events, with source srcaddr, until the connection fails; then it
// closes conn and removes key, the key conn was added under.
func (tcp *TCP) handleConn(conn net.Conn, key string, srcaddr ipv4port.IPv4Port) {
	// One decoder for the connection: a decoder reads ahead of the value it decodes, and the
	// bytes it read ahead belong to the next events.
	dec := json.NewDecoder(conn)
	for {
		ev := &events.Event{}
		slog.Debug("conn waiting for an event")
		if err := ev.FromDecoder(dec); err != nil {
			slog.Debug("failed to read an event", "err", err)
			break
		}

		slog.Debug("conn received an event", "type", ev.Type, "from", srcaddr.String())
		tcp.queue.Push(events.NewNetworkEvent(srcaddr, ev))
		slog.Debug("conn sent an event to the handler", "type", ev.Type, "from", srcaddr.String())
	}

	tcp.mu.Lock()
	if err := conn.Close(); err != nil {
		slog.Debug("failed to properly close an errored connection", "err", err)
	}
	// Remove the connection, unless Send already replaced it under key by a new one.
	if tcp.conns[key] == conn {
		delete(tcp.conns, key)
	}
	tcp.mu.Unlock()
}

var _ Network = (*TCP)(nil)
