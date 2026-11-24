// The Go model of package net over the net extension `netExt` (GooseLang/Ext/Net/Impl.lean;
// notes/net-tcp.md): the `[model]` table of Net/Code/net.toml splices this file into Go 1.27.3's
// net (goose/README.md, "Go model overlays"). linux/amd64.
//
// What is replaced is the layer under Go's own net code: the methods of `netFD` (the socket,
// over `internal/poll`'s FD and system calls), the socket-option functions, the listener's
// `accept` and `close`, `Listen`, `Dial`, `DialTimeout` (the resolver, sockets) and
// `TCPAddr.String` (`net/netip`'s formatting). The types (`conn`, `TCPConn`, `TCPListener`,
// `netFD`) and the methods above this layer (`conn.Read`, `TCPListener.Accept`, ...: the
// `ok()` checks, the `OpError`s) are Go's, translated. A model `netFD` holds the extension's id of
// its connection end or listener in Go's own `pfd.Sysfd` (in gc builds, the kernel fd): it is
// read by nothing outside net that the model translates (`SyscallConn`, `File` are not modelled).
//
// The `ext*` functions, `closedErr` and `stuck` are primitive stubs (`trusted` in net.toml):
// their models are Net/TrustedCode/net.lean's, each one extension operation (or the shared stuck
// point); their Go bodies serve gc builds only (examples/net and Go's own tests under the
// overlay), over plain blocking sockets: the common case, not the model.
//
// The extension's result codes (`Net.NetErr.code`): 0 success, 1 `closed`, 2 `timeout`, 3 `sys`;
// a read's 4 is EOF.

package net

import (
	"context"
	"internal/poll"
	"io"
	"os"
	"syscall"
	"time"
)

// ---- replaced declarations ----

// MODEL: netFD.Read (fd_posix.go: `fd.pfd.Read(p)`, poll.FD's loop over read(2) through the
// poller, wrapped by wrapSyscallError("read")): the extension's Read of len(p) bytes (D1, the
// outcomes of Linux's read(2) with Go's poller), the bytes copied into p; 0 bytes from a
// non-empty p is io.EOF, as poll.FD's ZeroReadIsEOF; an error is the kind's (kindErr).
func (fd *netFD) Read(p []byte) (n int, err error) {
	s, code := extRead(fd.pfd.Sysfd, len(p))
	if code == 0 {
		return copy(p, []byte(s)), nil
	}
	if code == 4 {
		return 0, io.EOF
	}
	return 0, kindErr(code, "read")
}

// MODEL: netFD.Write (fd_posix.go, poll.FD.Write's loop): a write(2) of p[nn:] with its wait is
// one step of the extension's Write (D2), which says whether it is the call's first (D25: the
// end's write lock, Go's fd.writeLock()), until a step fails or every byte is written. Go's
// maxRW chunks are among a step's outcomes (any prefix).
func (fd *netFD) Write(p []byte) (nn int, err error) {
	for {
		n, code := extWrite(fd.pfd.Sysfd, string(p[nn:]), nn == 0)
		nn += n
		if code != 0 {
			return nn, kindErr(code, "write")
		}
		if nn == len(p) {
			return nn, nil
		}
	}
}

// MODEL: netFD.Close (fd_posix.go, poll.FD.Close): the extension's Close (D3: success, or
// `closed` for a second close; Linux's close(2) of a socket does not fail).
func (fd *netFD) Close() error {
	return codeErr(extClose(fd.pfd.Sysfd), "close")
}

// MODEL: netFD.closeWrite (fd_posix.go: shutdown(2) with SHUT_WR, wrapSyscallError("shutdown")):
// the extension's CloseWrite (D4).
func (fd *netFD) closeWrite() error {
	return codeErr(extCloseWrite(fd.pfd.Sysfd), "shutdown")
}

// MODEL: netFD.SetDeadline (fd_posix.go, poll.FD.SetDeadline): the extension's SetDeadline of
// both deadlines (D5; the zero time clears them).
func (fd *netFD) SetDeadline(t time.Time) error {
	return codeErr(extSetDeadline(fd.pfd.Sysfd, 0, t), "set")
}

// MODEL: netFD.SetReadDeadline: the read deadline only (D5).
func (fd *netFD) SetReadDeadline(t time.Time) error {
	return codeErr(extSetDeadline(fd.pfd.Sysfd, 1, t), "set")
}

// MODEL: netFD.SetWriteDeadline: the write deadline only (D5).
func (fd *netFD) SetWriteDeadline(t time.Time) error {
	return codeErr(extSetDeadline(fd.pfd.Sysfd, 2, t), "set")
}

// MODEL: netFD.accept (fd_unix.go: accept4(2) through the poller, ECONNABORTED retried, errors
// wrapped by wrapSyscallError("accept4")): the extension's Accept (D7); the new socket's addresses
// arbitrary (D18), its network the listener's (Go's newFD(d, fd.family, fd.sotype, fd.net)).
func (fd *netFD) accept() (netfd *netFD, err error) {
	id, code := extAccept(fd.pfd.Sysfd)
	if code != 0 {
		return nil, kindErr(code, "accept4")
	}
	return modelFD(id, fd.net, anyTCPAddr(), anyTCPAddr()), nil
}

// MODEL: setReadBuffer (sockopt_posix.go: SO_RCVBUF, wrapSyscallError("setsockopt")): the
// extension's SetSockopt of an option of no validity condition (D24; Linux clamps the value).
func setReadBuffer(fd *netFD, bytes int) error {
	return codeErr(extSetSockopt(fd.pfd.Sysfd, 0, 0), "setsockopt")
}

// MODEL: setWriteBuffer (SO_SNDBUF), as setReadBuffer.
func setWriteBuffer(fd *netFD, bytes int) error {
	return codeErr(extSetSockopt(fd.pfd.Sysfd, 0, 0), "setsockopt")
}

// MODEL: setKeepAlive (SO_KEEPALIVE), whatever the value (D24).
func setKeepAlive(fd *netFD, keepalive bool) error {
	return codeErr(extSetSockopt(fd.pfd.Sysfd, 0, 0), "setsockopt")
}

// MODEL: setLinger (SO_LINGER), whatever the value (D24: a resetting Close is a cut, D1).
func setLinger(fd *netFD, sec int) error {
	return codeErr(extSetSockopt(fd.pfd.Sysfd, 0, 0), "setsockopt")
}

// MODEL: setNoDelay (tcpsockopt_posix.go: TCP_NODELAY), whatever the value (D24).
func setNoDelay(fd *netFD, noDelay bool) error {
	return codeErr(extSetSockopt(fd.pfd.Sysfd, 0, 0), "setsockopt")
}

// MODEL: setKeepAliveIdle (tcpsockopt_unix.go: TCP_KEEPIDLE of d rounded up to seconds, the
// default for 0, nothing for d < 0): the extension's SetSockopt of kind 1 with d, whose
// arithmetic the extension's keepIdleValid transcribes (D24).
func setKeepAliveIdle(fd *netFD, d time.Duration) error {
	return codeErr(extSetSockopt(fd.pfd.Sysfd, 1, int64(d)), "setsockopt")
}

// MODEL: TCPListener.accept (tcpsock_posix.go): Go's code but newTCPConn's setup of the new
// connection (TCP_NODELAY and the listener's keep-alive options, their errors ignored by Go; what
// they change in the kernel is not observable beyond D1's cuts, D24), and with it its reads of
// the test hooks testPreHookSetKeepAlive and testHookSetKeepAlive (nil outside net's tests).
func (ln *TCPListener) accept() (*TCPConn, error) {
	fd, err := ln.fd.accept()
	if err != nil {
		return nil, err
	}
	return &TCPConn{conn{fd}}, nil
}

// MODEL: TCPListener.close (tcpsock_posix.go: ln.fd.Close(), close(2) of the listening socket):
// the extension's LisClose (D9), the extension's operation on a listener.
func (ln *TCPListener) close() error {
	return codeErr(extLisClose(ln.fd.pfd.Sysfd), "close")
}

// MODEL: Listen (dial.go: ListenConfig.Listen with the zero ListenConfig: the address resolved,
// socket(2), setsockopt, bind(2), listen(2)): for "tcp" and "tcp4" (D23; any other network is not
// modelled: stuck), the extension's Listen of the address (D6); the listener's address arbitrary
// (D18); an error is Go's `&OpError{Op: "listen", Net: network, Addr: <the resolved address>}`,
// the address arbitrary and the failing system call's name too (any of Go's).
func Listen(network, address string) (Listener, error) {
	if !netOk(network) {
		stuck()
	}
	id, code := extListen(address)
	if code == 0 {
		return &TCPListener{fd: modelFD(id, network, anyTCPAddr(), nil)}, nil
	}
	return nil, &OpError{Op: "listen", Net: network, Source: nil, Addr: anyTCPAddr(),
		Err: kindErr(code, extAnyString())}
}

// MODEL: Dial (dial.go: Dialer.Dial with the zero Dialer: the address resolved, socket(2),
// connect(2) and the handshake's wait): for "tcp" and "tcp4" (D23), the extension's Dial (D8,
// D16); the connection's addresses arbitrary (D18); an error is Go's `&OpError{Op: "dial", Net:
// network, Addr: <the resolved address>}` (dialSingle), as Listen's.
func Dial(network, address string) (Conn, error) {
	if !netOk(network) {
		stuck()
	}
	id, code := extDial(address)
	if code == 0 {
		return newConn(id, network), nil
	}
	return nil, &OpError{Op: "dial", Net: network, Source: nil, Addr: anyTCPAddr(),
		Err: kindErr(code, extAnyString())}
}

// MODEL: DialTimeout (dial.go: Dialer{Timeout: timeout}.Dial), as Dial (D19); a failure's Err is
// the system's error or a timeout: errTimeout (mapErr(ctx.Err()) once the dial's context expired)
// or poll.ErrDeadlineExceeded (netFD.connect's wait under the dial's deadline). The timeout's value
// is not modelled (any timeout may expire, as D5's deadlines).
func DialTimeout(network, address string, timeout time.Duration) (Conn, error) {
	if !netOk(network) {
		stuck()
	}
	id, code := extDial(address)
	if code == 0 {
		return newConn(id, network), nil
	}
	var err error
	if extAnyBool() {
		err = kindErr(code, extAnyString())
	} else if extAnyBool() {
		err = errTimeout
	} else {
		err = poll.ErrDeadlineExceeded
	}
	return nil, &OpError{Op: "dial", Net: network, Source: nil, Addr: anyTCPAddr(), Err: err}
}

// MODEL: TCPAddr.String (tcpsock.go: JoinHostPort of ipEmptyString(a.IP), the zone and the port;
// IP.String formats through net/netip, which nothing translates): an arbitrary string. Go's
// String always returns (a nil receiver gives "<nil>"), with no other effect.
func (a *TCPAddr) String() string {
	return extAnyString()
}

// ---- additions (translated) ----

// netOk: the networks the model has (D23): "tcp", and "tcp4", which behaves as "tcp" on the
// IPv4 addresses the extension accepts.
func netOk(nw string) bool {
	return nw == "tcp" || nw == "tcp4"
}

// modelFD: a netFD for the extension's id `id` (in pfd.Sysfd), on the network nw, with the
// addresses la and ra (Go's newFD and setAddr; the other fields are read only by code the model
// does not translate).
func modelFD(id int, nw string, la, ra Addr) *netFD {
	return &netFD{pfd: poll.FD{Sysfd: id}, net: nw, laddr: la, raddr: ra}
}

// newConn: a new *TCPConn (Go's newTCPConn, as TCPListener.accept's model) for the connection
// end `id`, with arbitrary addresses (D18).
func newConn(id int, nw string) *TCPConn {
	la := anyTCPAddr()
	ra := anyTCPAddr()
	return &TCPConn{conn{modelFD(id, nw, la, ra)}}
}

// anyTCPAddr: a new *TCPAddr with arbitrary fields (D18: Go's sockaddrToTCP of getsockname or
// getpeername; never nil for a connected or bound IPv4 socket).
func anyTCPAddr() Addr {
	return &TCPAddr{IP: IP([]byte(extAnyString())), Port: int(extAnyW64()), Zone: extAnyString()}
}

// kindErr: the error of a failure of code `code` (D14): poll.ErrNetClosing for `closed` (Go's
// errClosing), poll.ErrDeadlineExceeded for `timeout`, and for `sys` the system call's error as
// wrapSyscallError wraps it, `&os.SyscallError{name, Errno(n)}` with n arbitrary and nonzero.
func kindErr(code uint64, name string) error {
	if code == 1 {
		return closedErr()
	}
	if code == 2 {
		return poll.ErrDeadlineExceeded
	}
	return &os.SyscallError{Syscall: name, Err: extAnyErrno()}
}

// codeErr: nil for success, else kindErr.
func codeErr(code uint64, name string) error {
	if code == 0 {
		return nil
	}
	return kindErr(code, name)
}

// ---- primitive stubs (trusted; Go bodies for gc builds only) ----

// extListen: the extension's Listen of the address (the listener's id, the result's code).
func extListen(address string) (int, uint64) {
	l, err := (&ListenConfig{}).Listen(context.Background(), "tcp", address)
	if err != nil {
		return 0, 3
	}
	return detach(l.(*TCPListener).fd)
}

// extDial: the extension's Dial of the address (the end's id, the code).
func extDial(address string) (int, uint64) {
	c, err := (&Dialer{}).DialContext(context.Background(), "tcp", address)
	if err != nil {
		return 0, 3
	}
	return detach(c.(*TCPConn).fd)
}

// extAccept: the extension's Accept on the listener id.
func extAccept(id int) (int, uint64) {
	nfd, _, err := syscall.Accept4(id, syscall.SOCK_CLOEXEC)
	if err != nil {
		return 0, errnoCode(err)
	}
	return nfd, 0
}

// extRead: the extension's Read of n bytes at the end id (the bytes, the code; 4 for EOF).
func extRead(id int, n int) (string, uint64) {
	if n == 0 {
		return "", 0
	}
	b := make([]byte, n)
	k, err := syscall.Read(id, b)
	if err != nil {
		return "", errnoCode(err)
	}
	if k == 0 {
		return "", 4
	}
	return string(b[:k]), 0
}

// extWrite: one step of the extension's Write of bs at the end id (the count written, the code);
// first says whether it is the call's first step.
func extWrite(id int, bs string, first bool) (int, uint64) {
	k, err := syscall.Write(id, []byte(bs))
	if err != nil {
		return 0, errnoCode(err)
	}
	return k, 0
}

// extClose: the extension's Close of the end id.
func extClose(id int) uint64 {
	syscall.Shutdown(id, syscall.SHUT_RDWR)
	if err := syscall.Close(id); err != nil {
		return errnoCode(err)
	}
	return 0
}

// extLisClose: the extension's LisClose of the listener id.
func extLisClose(id int) uint64 {
	return extClose(id)
}

// extCloseWrite: the extension's CloseWrite of the end id.
func extCloseWrite(id int) uint64 {
	if err := syscall.Shutdown(id, syscall.SHUT_WR); err != nil {
		return errnoCode(err)
	}
	return 0
}

// extSetDeadline: the extension's SetDeadline of the deadlines of kind `kind` (0 both, 1 read,
// 2 write) of the end id, to t (its model reads t's two words).
func extSetDeadline(id int, kind uint64, t time.Time) uint64 {
	var tv syscall.Timeval
	if !t.IsZero() {
		d := time.Until(t)
		if d <= 0 {
			d = time.Microsecond
		}
		tv = syscall.NsecToTimeval(d.Nanoseconds())
	}
	if kind != 2 {
		if err := syscall.SetsockoptTimeval(id, syscall.SOL_SOCKET, syscall.SO_RCVTIMEO, &tv); err != nil {
			return errnoCode(err)
		}
	}
	if kind != 1 {
		if err := syscall.SetsockoptTimeval(id, syscall.SOL_SOCKET, syscall.SO_SNDTIMEO, &tv); err != nil {
			return errnoCode(err)
		}
	}
	return 0
}

// extSetSockopt: the extension's SetSockopt of kind `kind` (1 TCP_KEEPIDLE of the duration x, 0
// the others) at the end id.
func extSetSockopt(id int, kind uint64, x int64) uint64 {
	if kind == 1 && x > 0 {
		secs := int((time.Duration(x) + time.Second - 1) / time.Second)
		if err := syscall.SetsockoptInt(id, syscall.IPPROTO_TCP, syscall.TCP_KEEPIDLE, secs); err != nil {
			return errnoCode(err)
		}
	}
	return 0
}

// extAnyString: the extension's AnyString, an arbitrary string.
func extAnyString() string { return "" }

// extAnyW64: the extension's AnyW64, an arbitrary word.
func extAnyW64() uint64 { return 0 }

// extAnyBool: the extension's AnyBool, an arbitrary boolean.
func extAnyBool() bool { return true }

// extAnyErrno: the extension's AnyErrno, an arbitrary nonzero errno.
func extAnyErrno() syscall.Errno { return syscall.EIO }

// closedErr: poll.ErrNetClosing as an error (errNetClosing{}, the only value of its type, which
// net cannot name).
func closedErr() error { return poll.ErrNetClosing }

// stuck: no behaviour (the shared stuck point, internal/gomodel.Stuck's model).
func stuck() { select {} }

// detach (gc builds only, used by the stubs' bodies): the fd of a socket Go's own code made, as
// a plain blocking socket the stubs use, the netFD Go made closed.
func detach(fd *netFD) (int, uint64) {
	id, _, err := fd.pfd.Dup()
	fd.pfd.Close() // sets Sysfd to -1: the finalizer's later Close is extClose(-1), a no-op
	if err != nil {
		return 0, 3
	}
	syscall.SetNonblock(id, false)
	return id, 0
}

// errnoCode (gc builds only): an errno's code: EBADF `closed`, EAGAIN (a socket timeout)
// `timeout`, any other `sys`.
func errnoCode(err error) uint64 {
	if err == syscall.EBADF {
		return 1
	}
	if err == syscall.EAGAIN {
		return 2
	}
	return 3
}
