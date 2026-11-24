// Package semantics measures, by tests over real TCP, each decision of the TCP
// extension's trusted semantics (GooseLang/Ext/Net/Impl.lean: the steps
// ReadStep, WriteStep, CloseStep, CloseWriteStep, SetDeadlineStep, ListenStep,
// AcceptStep, DialStep, LisClose and the node crash; each operation's outcome
// is a relation there: ReadOutcome, WriteOutcome, CloseOutcome,
// CloseWriteOutcome, DeadlineOutcome, LisCloseOutcome; the addresses addrOk,
// listenOk, lisAccepts), and of the
// trusted net models (Net/TrustedCode/net.lean), numbered D1-D25 as in
// Impl.lean's header:
//
//	D1  ReadStep         D8   DialStep              D15 a Write is a loop of steps (WriteOutcome)
//	D2  WriteStep        D9   LisClose              D16 abandoned dials (DialStep, NetConn.abandoned)
//	D3  CloseStep        D10  crash (a node's listeners go; connections untouched)
//	D4  CloseWriteStep   D11  process exit: as a crash, for the peers
//	D5  SetDeadlineStep  D12  not modeled (ENOMEM/ENOBUFS, other addresses, ...)
//	D6  ListenStep       D13  the deployment     D17 Close of an open end or listener succeeds
//	D7  AcceptStep       D14  the error kinds    D18 addresses (TrustedCode/net.lean)
//	                                             D19 DialTimeout (TrustedCode/net.lean)
//	                                             D20 valid addresses (addrOk, portOk)
//	                                             D21 wildcard Listen (wildOk, lisAccepts)
//	                                             D22 steps: every operation may stutter
//	                                                 (waiting); invalid uses panic (NetStep)
//	                                             D23 the network "tcp4" (TrustedCode/net.lean)
//	                                             D24 socket options (SetSockoptStep, SockOptOutcome)
//	                                             D25 the write lock (WriteStep, NetConn.lock)
//	                                             D26 initial states (NetLocal.init, NetGlobal.init)
//
// Each test is one behavior: its doc comment says the decision it supports or
// refutes, what Linux and Go do, and why (the kernel or Go code path). Every
// measured outcome is Go 1.27.3 (linux/amd64), Linux 7.0.0-38-generic, over
// 127.0.0.1 with kernel-chosen ports, the tests in parallel (go test
// -count=100 passed for the v2 tests, -count=10 for v3_test.go). Where the
// kernel's timing matters, a test waits (bounded) on a probe that changes
// nothing (the TCP state from TCP_INFO, the unread count from SIOCINQ:
// helpers_test.go), never on a sleep. The process tests re-run the test
// binary as a child (child_test.go) and kill it with SIGKILL, or let it exit.
//
// The rule (CLAUDE.md): every change to the trusted semantics adds or updates
// the test of the decision it changes, in the same commit.
//
// Index. Each row: the test; the decisions; what it establishes; the class of
// its evidence (measured: the test; documented: a cited source; assumed: no
// evidence, an assumption every theorem makes); the Lean definition, and the
// example of GooseLang/Ext/Net/Tests.lean that checks the relation allows (or
// excludes) the outcome (by the test's name in its comment).
//
// Reads (read_test.go):
//
//	TestReadPartial              D1   a Read returns what arrived (k <= min(n, unread)), the rest stays;   measured   ReadOutcome, ReadAvail
//	                                  never more than asked
//	TestReadEmptyBuffer          D1   empty Read: 0, nil at once, even with bytes, an expired deadline     measured   ReadOutcome (n = 0)
//	                                  or a pending RST (not consumed); ErrClosed after own Close
//	TestReadEOFAfterFin          D1,D3 the bytes, then EOF, then EOF again                                 measured   ReadAvail (EOF)
//	(in-order delivery)          D1,D2 a Read's bytes are the oldest unread ones, uncorrupted, once       assumed    ReadAvail (take/drop)
//
// Resets (reset_test.go):
//
//	TestResetCloseUnreadInput    D1,D3 Close with unread input sends RST; the peer reads the bytes        measured   ReadOutcome (break), NetErr.sys
//	                                  it had received, then ECONNRESET, then EOF
//	TestResetLingerZero          D1   SetLinger(0)+Close: the same                                         measured   ReadOutcome (break)
//	TestResetErrorTakenByWrite   D1,D2 the reset error goes to the first call: a Write takes it, then     measured   WriteOutcome (cut)
//	                                  the reads are the bytes then EOF, no error (peer Closed: d fin)
//	TestWriteAfterPeerClose      D2   a Write after the peer's FIN succeeds, bytes lost; after the RST    measured   WriteOutcome (cut)
//	                                  every Write fails (EPIPE: RST in CLOSE_WAIT); the Read is EOF
//	TestPartialWriteOnReset      D2   a Write cut by a RST returns 0 < n < len, ECONNRESET                 measured   WriteOutcome (open: steps, then sys, cut)
//
// Sticky read errors (sticky_test.go, sticky_netns_test.go; notes/net-sticky-read.md; D1 v3.5,
// Impl.lean's ReadAvail: a sys read error only once nothing is unread, so that no byte follows a
// read error but a deadline's timeout):
//
//	TestStickyEOF                D1   FIN: the bytes, EOF, EOF ...; a later RST (peer's Close with      measured   ReadAvail (EOF; sticky
//	                                  unread input) changes nothing, EOF (SOCK_DONE before sk_err);                 already)
//	                                  a Write after EOF succeeds, after the RST EPIPE
//	TestStickyReset              D1,D14 a RST with bytes received: the bytes, then ECONNRESET with 0     measured   ReadAvail (sys: v3.5,
//	                                  unread (SIOCINQ), then EOF on every Read; an expired deadline:                d.bytes = [])
//	                                  timeout; an empty Read (0, nil); Writes EPIPE
//	TestStickyResetBlockedRead   D1,D14 a RST while a Read waits: ECONNRESET, then EOF                   measured   ReadOutcome (break)
//	TestStickyKilledPeer         D1,D10,D11 a killed or exited peer with unread input: the bytes,        measured   ReadOutcome (break)
//	                                  ECONNRESET with 0 unread, then EOF; Write EPIPE
//	TestStickyOwnClose           D1,D3 own Close with bytes unread: ErrClosed on every Read and Write   measured   NetEnd.closed
//	TestStickyNotTimeout         D1,D5 the exception: after a read deadline's timeout (blocked, or       measured   ReadAvail (timeout: d' = d)
//	                                  expired with bytes unread) the bytes follow once it is cleared
//	TestStickyTimedOut           D1,D14 (network namespaces) the kernel gives up with bytes received:    measured   ReadAvail (sys: v3.5,
//	                                  the bytes, then ETIMEDOUT (a partition) or EHOSTUNREACH (an ICMP              d.bytes = [])
//	                                  host-unreachable: sk_err_soft) with 0 unread, then EOF; Write EPIPE
//
// Writes (write_test.go, v3_test.go):
//
//	TestEmptyWrite               D2   an empty Write (one step): (0, nil) live; (0, timeout) with an      measured   WriteOutcome
//	                                  expired write deadline; (0, ECONNRESET) then (0, EPIPE) after a
//	                                  RST; (0, EPIPE) after CloseWrite
//	TestWriteCloseRace           D15  a Write blocked when another goroutine Closes the end: 0 < k < len, measured   WriteOutcome (steps, Close,
//	                                  ErrClosed; the peer reads exactly k bytes, then EOF                            then closed), CloseOutcome
//	TestWriteDeadlineSetDuring   D2,D15 a Write blocked when another goroutine sets its deadline, after  measured   WriteOutcome (steps, SetDeadline,
//	                                  the peer read some of it: 0 < n < len, os.ErrDeadlineExceeded;                 then timeout), DeadlineOutcome
//	                                  the peer reads exactly n bytes, then EOF (REFUTED v3's one-step
//	                                  Write; allowed since v3.1)
//	(the Write loop)             D2   poll.FD.Write is writeLock, prepareWrite, then write(2) of p[nn:]   documented conn.Write.impl (a step per
//	                                  until nn == len(p), waitWrite on EAGAIN: each write(2) with its                write(2)), WriteOutcome
//	                                  wait a step; a short Write only with an error (nn, err; err nil
//	                                  once nn == len(p) but for an empty p); a failing write(2) writes
//	                                  nothing (internal/poll/fd_unix.go; Linux tcp_sendmsg_locked)
//
// Close, CloseWrite (close_test.go, v3_test.go):
//
//	TestCloseTwice               D1-D5,D17 Close: nil, FIN; after it every operation errs, ErrClosed     measured   CloseOutcome, NetErr.closed
//	TestCloseUnblocksRead        D1,D3 own Close wakes a blocked Read with ErrClosed                     measured   ReadOutcome (closed)
//	TestCloseAfterReset          D3,D5,D17 Close and SetDeadline of a reset end: nil                     measured   CloseOutcome, DeadlineOutcome
//	TestCloseOpenNil             D17  Close of an open end (fresh, after FIN, after CloseWrite, after a   measured   CloseOutcome, LisCloseOutcome
//	                                  RST, a Read blocked) and of an open listener: nil (poll.FD.Close;
//	                                  close(2) of a socket returns 0: documented, Linux sock_close)
//	TestCloseWrite               D1,D2,D4 peer reads the bytes then EOF; own Write: EPIPE; own Read     measured   CloseWriteOutcome, WriteOutcome (fin)
//	                                  still works; CloseWrite again: nil, then ENOTCONN after both FINs
//	TestCloseWriteAfterReset     D4   CloseWrite of a reset end: ENOTCONN, the reset error kept          measured   CloseWriteOutcome (sys)
//
// Deadlines (deadline_test.go):
//
//	TestReadDeadlineLosesNothing D1,D5 a timeout consumes no byte (expired: timeout even with bytes);   measured   ReadAvail (timeout), DeadlineOutcome
//	                                  time.Time{} clears it; no timeout without a deadline
//	TestWriteDeadlinePrefix      D2,D5 a Write past its deadline: 0 < n < len, timeout; exactly n bytes measured   WriteOutcome (steps, then timeout)
//	                                  reach the peer, the connection stays usable
//
// Listeners, Dial (listen_test.go, v3_test.go):
//
//	TestListenTwice              D6   EADDRINUSE at an open listener's address; success after its Close measured   ListenStep
//	TestListenTakenByOtherProcess D6  another process's listener: EADDRINUSE too (the model also allows  measured   ListenStep
//	                                  success: more than Linux)
//	TestListenNotLocal           D6,D13 an address that is not this machine's (192.0.2.1, TEST-NET-1):    measured   ListenStep (sys), listenOk
//	                                  EADDRNOTAVAIL, an *OpError around an *os.SyscallError (bind):
//	                                  the model's sys failure (v3.4: no plan, any machine may listen
//	                                  at any valid address; the kernel refuses one not its own)
//	TestDialRefused              D8   no listener: ECONNREFUSED                                          measured   DialStep (sys)
//	TestAcceptAfterListenerClose D7,D9,D17 LisClose: nil, wakes Accept with ErrClosed; Accept and Close  measured   AcceptStep, LisCloseOutcome
//	                                  after it: ErrClosed
//	TestPendingAtListenerClose   D7-D9 a dialed, unaccepted connection is reset by the listener's Close; measured   AcceptStep
//	                                  a new listener does not get it (Linux excludes what D7 allows)
//	TestDialTimeoutAccepted      D16,D19 a failed DialTimeout's connection is accepted, reading EOF,      measured   DialStep (abandoned), DialTimeout.impl
//	                                  never data; its Err a timeout (both os.ErrDeadlineExceeded and
//	                                  errTimeout occur) or an *os.SyscallError
//
// Error values (errors_test.go, v3_test.go):
//
//	TestErrorsAreOpErrors        D14  every failure an *OpError, Net "tcp", Op read/write/close/          measured   model.opError
//	                                  set/dial/listen/accept; EOF is io.EOF itself; Error()             measured   OpError.Error.impl
//	                                  never empty (it starts with Op)
//	TestErrClosed                D14  own closed end or listener (also a blocked Read, Accept): Err is     measured   NetErr.closed, model.closedErr
//	                                  net.ErrClosed, Timeout/Temporary false; no other failure Is it
//	TestDeadlineErrors           D14  a Read or Write deadline: Err is os.ErrDeadlineExceeded itself,     measured   NetErr.timeout, model.deadlineErr
//	                                  Timeout/Temporary true
//	TestSyscallErrors            D14  other failures: *os.SyscallError{read|write|shutdown|connect|bind}  measured   NetErr.sys, model.sysErr
//	                                  around an Errno; the OpError's Source and Addr per operation
//	(Timeout of sys errors)      D14  an Errno's Timeout/Temporary: ETIMEDOUT, EAGAIN true (syscall_unix.go documented model.errFlag (arbitrary)
//	                                  Errno.Timeout), so OpError.Timeout is arbitrary for sys errors
//	TestZeroValues               D12,D22 a zero TCPConn/TCPListener: bare syscall.EINVAL, no socket       measured   model.einval (the models' id-0 check,
//	                                  touched                                                                         before the extension: net.lean)
//
// Addresses (addr_test.go, v3_test.go, listen_test.go; Impl.lean addrOk, wildOk, lisAccepts). v3.4
// (2026-11-20): no plan and no hosts. Any machine may listen at any valid address (addrOk) or
// valid wildcard (wildOk): a Listen at an address that is not the machine's fails
// (TestListenNotLocal, EADDRNOTAVAIL), which the model allows as sys; a Listen at one that is
// another machine's (on that machine) is the proofs' business (a ghost token per address), and
// the closed world below. A wildcard listener takes connections dialed to any address with its
// port (lisAccepts): Linux, every local address with the port (TestAddressAliases,
// TestWildcardListen); the model, any address, a superset (sound: a connection the kernel
// delivers to it is one the model lets it accept).
//
//	TestAddressAliases           D13,D20,D21 "localhost:P", ":P" reach 127.0.0.1:P's listener; ":P"'s measured   addrOk (excludes them as Dial
//	                                  listener takes 127.0.0.1:P, 127.0.0.2:P; Listen(127.0.0.1:P) with              addresses), lisAccepts (a wildcard
//	                                  ":P" open: EADDRINUSE                                                          takes any address with its port)
//	TestWildcardListen           D21  ":P", "0.0.0.0:P", "[::]:P" listen, Addr "[::]:P", accept a Dial  measured   wildOk, wildPort, lisAccepts
//	                                  of 127.0.0.1:P, conflict with Listen(127.0.0.1:P) (EADDRINUSE: a
//	                                  sys failure the model allows; it also allows success)
//	TestAddrs                    D18  LocalAddr, RemoteAddr, Addr: non-nil *TCPAddr, the same at every    measured   model.anyTCPAddr, conn.LocalAddr
//	                                  call, after a reset and after Close; zero TCPConn's nil; zero
//	                                  TCPListener's Addr panics
//	(the closed world)           D13  no process but the deployment's nodes, on any machine, accepts a    assumed    (prose: Impl.lean D13)
//	                                  connection a node dials or dials one a node's listener can accept
//	(ephemeral ports)            D20  a port outside 32768-60999 cannot be a Dial's own source port       documented portOk, addrOk (Linux
//	                                  (ip_local_port_range's default; Go's selfConnect: tcpsock_posix.go)            ip_local_port_range)
//
// Process death (process_test.go):
//
//	TestKilledWriterFin          D1,D10,D11 the bytes, then EOF, no error (kernel FIN)                   measured   ReadOutcome (break)
//	TestKilledWithUnreadInput    D1,D10,D11 the bytes, then ECONNRESET, then EOF (kernel RST)            measured   ReadOutcome (break)
//	TestKilledResetTakenByWrite  D1,D2,D10 Write takes the RST's error; reads: bytes then EOF, no error  measured   ReadOutcome (break)
//	TestWriteToKilledPeer        D2,D10 a Write after the FIN succeeds (lost); after the RST: EPIPE      measured   WriteOutcome (cut)
//	TestServerKilledBeforeReply  D1,D10,D11 the client reads EOF, no bytes, no error                     measured   ReadOutcome (break)
//	TestKilledListener           D7,D8,D10 the queued connection is reset; Dial then refused             measured   AcceptStep, DialStep
//
// Initial states (init_test.go; since 2026-11-22 the semantics' initLocal/initGlobal, net_semantics):
//
//	TestFreshProcessNoSocket     D26  a process started by os/exec has no socket among its fds, though   measured   NetLocal.init (initLocal)
//	                                  its parent holds a listener and a connection (CLOEXEC)
//	(the network at the start)   D13,D26 no connection before the deployment's processes start: none    assumed    NetGlobal.init (initGlobal)
//	                                  exists yet, and no other process dials or accepts (closed world)
//
// Steps (D22; Impl.lean's header has the table of every operation's outcomes in every state):
//
//	(the stutter convention)     D22  every operation may take a step that changes nothing; a blocked     documented NetStep, IsNetStep, OrInvalid;
//	                                  Read, Accept, Write step is that stutter until an outcome decides            Tests.lean: isNetStep_total,
//	                                  it; every state has an outcome besides it; an argument the                   isNetStep_result
//	                                  extension cannot use (an invalid address: D13, D20, D21; an id
//	                                  naming nothing) panics (GooseLang's stuck Panic). The convention
//	                                  of Perennial's Grove extension (Perennial/GooseLang/Ext/Grove/
//	                                  Impl.lean, GroveStep); no Go behavior of its own: a stutter is
//	                                  never a call's last step
//
// v3.3 (tcp4_test.go, sockopt_test.go, writelock_test.go; notes/dsverify-net-port-plan.md, phase 2):
//
//	TestTcp4                     D23  "tcp4" as "tcp" on valid IPv4 addresses (Listen, Dial, DialTimeout,  measured   model.netOk, conn's and TCPListener's
//	                                  the wildcards ":P", "0.0.0.0:P", "[::]:P" every IPv4 address);                net field, model.opError's network
//	                                  every *OpError's Net the network string: Dial's and Listen's
//	                                  the call's, a connection's its Dial's or its listener's (Read,
//	                                  Write, Close, SetDeadline, CloseWrite, SetKeepAlive, Accept,
//	                                  the listener's Close); "tcp" and "tcp4" ends interoperate
//	TestSockOpts                 D24  SetKeepAlive, SetKeepAlivePeriod, SetReadBuffer, SetWriteBuffer,     measured   SockOptOutcome, sockOptValid,
//	                                  SetNoDelay, SetLinger: nil on an end not closed, in any state                  keepIdleValid, model.sockOpt
//	                                  (fresh, after FIN, CloseWrite, a reset; dialer's and acceptor's
//	                                  from an MPTCP listener); ErrClosed in an *OpError "set" on a
//	                                  closed end (TCPConn's: Source laddr, Addr raddr; conn's buffer
//	                                  sizes: Source nil, Addr laddr); EINVAL (setsockopt) for a
//	                                  keepalive period over 32767 s (int32 of the rounded-up seconds:
//	                                  (2^32+10) s is 10 s); a negative period: nil, no system call,
//	                                  even closed; the zero value: bare EINVAL
//	(2^20 waiters)               D25  a known limitation, not modeled: Go's fdMutex panics past         not modeled (Impl.lean's "Known
//	                                  1048575 calls waiting on one socket's lock (fd_mutex.go); the                 limitation"; review F1)
//	                                  model lets them wait (review F1)
//	(no other state)             D24  the options change nothing a Read or Write result shows beyond     assumed    (no state: SockOptOutcome)
//	                                  what the relations already allow (keepalive's effect is a cut;
//	                                  buffer sizes only change when a step blocks: a stutter)
//	TestWriteLock                D25  four concurrent 4 MiB Writes on one end to a slow reader: each      measured   WriteStep (first, NetConn.lock),
//	                                  Write's bytes contiguous in the stream, every Write complete; a                writeLast; Tests.lean: the
//	                                  Write waiting for the lock when the end is Closed: (0, ErrClosed)              interleaving excluded
//	                                  after the holder's (internal/poll/fd_unix.go: FD.Write holds
//	                                  fd.writeLock() over its whole loop; fdMutex.rwlock fails once
//	                                  closing)
//
// Network faults, in network namespaces (netns_test.go; NET_NETNS=1, re-run as root by sudo -n;
// client, router and server namespaces, the faults in the router's FORWARD chain):
//
//	TestTimeoutOnBreak           D1,D2,D14 a partition, the kernel gives up (TCP_USER_TIMEOUT 2s, a     measured   ReadOutcome (break), WriteOutcome
//	                                  Read or a 16 MiB Write blocked; keepalive 1s/1s/2 idle): ETIMEDOUT            (open: sys, cut), NetErr.sys,
//	                                  as *OpError > *os.SyscallError > Errno, Timeout() and Temporary()               model.errFlag (arbitrary for sys)
//	                                  true, not ErrDeadlineExceeded; the Write (110048, ETIMEDOUT); bytes
//	                                  written before lost; then EOF, EOF, EPIPE, EPIPE; the peer, healed:
//	                                  Write nil, then ECONNRESET, EOF, EPIPE
//	TestResetInNetwork           D1,D2,D14 a middlebox's RST (iptables REJECT tcp-reset): received unread  measured   ReadOutcome (break), WriteOutcome (cut)
//	                                  bytes survive; Read first: bytes, ECONNRESET, EOF, then EPIPE; Write
//	                                  first: ECONNRESET, EPIPE, then bytes, EOF; the bytes that drew it
//	                                  lost; the other end: its bytes, then (healed) Write nil, ECONNRESET,
//	                                  EOF, EPIPE
//	TestPartitionHealed          D1,D2 a 2 s partition shorter than every timeout, healed: every byte     measured   ReadOutcome, WriteOutcome (no break)
//	                                  both ways once, in order, no error (Writes block up to 2.9 s)
//	TestStickyTimedOut           D1,D14 (sticky_netns_test.go) the kernel gives up on a connection    measured   ReadAvail (sys)
//	                                  with bytes received: the bytes, then ETIMEDOUT or EHOSTUNREACH, then
//	                                  EOF (above, "Sticky read errors")
//	TestAcceptOrder              D7   8 pending: back-to-back Dials accepted in Dial order (0/50 out of    measured   AcceptStep (any pending connection)
//	                                  order); concurrent ones 47-50/50 out of Dial-return order
//
// UDP (udp_*_test.go; the UDP extension, GooseLang/Ext/Udp/Impl.lean, version u1, decisions
// U1-U13; notes/net-udp.md). Go 1.27.3, Linux 7.0.0-1014-aws (2026-11-24): the plain tests
// over 127.0.0.1 with explicit ports of 20000-29999 (outside the ephemeral range, as addrOk
// requires), go test -count=3; the UDPNetns tests (udp_netns_test.go) in the client, router
// and server namespaces above (veth pairs, MTU 1500), NET_NETNS=1 -run UDPNetns, re-run as root:
//
//	TestUDPListenForms           U1   ListenUDP("udp4") at a.b.c.d:p: the 4-byte IP, the 16-byte      measured   udpAddrOf, ipv4Of, ValidDest,
//	                                  IPv4-mapped one and a junk Zone all bind the same a.b.c.d:p                    ListenStep
//	                                  (ipToSockaddrInet4: ip.To4(), the Zone ignored)
//	TestUDPListenTwice           U1   a second bind of an open socket's address: EADDRINUSE as          measured   ListenStep (sys; success also
//	                                  *OpError{listen, udp4, Source nil, Addr the laddr} >                           allowed: more than Linux)
//	                                  *os.SyscallError{bind} > Errno 98; SO_REUSEADDR 0, SO_REUSEPORT
//	                                  0 (SO_BROADCAST 1); after Close it binds
//	TestUDPListenNotLocal        U1   a non-local IP (192.0.2.1): EADDRNOTAVAIL, the same shape         measured   ListenStep (sys)
//	TestUDPAndTCPSamePort        U1   a TCP listener and a UDP socket at one ip:port coexist, both work  measured   udpExt apart from netExt
//	TestUDPSendDelivered         U2,U3 WriteToUDP (len, nil); received byte for byte (1, 100, 1472     measured   SendStep, Intact, RecvStep
//	                                  bytes), the source the sender's address
//	TestUDPSendToUnbound         U2   10 sends to an unbound port: (len, nil) each; the unconnected     measured   SendStep (success)
//	                                  sender's reads never ECONNREFUSED (__udp4_lib_err: no IP_RECVERR);
//	                                  control: a DialUDP socket gets ECONNREFUSED (not modeled)
//	TestUDPSendSizeLimit         U2,U3 loopback: 65507 bytes delivered whole; 65508: (0, *OpError       measured   SendStep (sys), Intact
//	                                  {write, udp4, Source laddr, Addr dest} > *os.SyscallError{sendto}
//	                                  > EMSGSIZE), nothing arrives
//	TestUDPZeroLength            U2,U4 an empty datagram: WriteToUDP (0, nil), ReadFromUDP (0, sender,   measured   SendStep, RecvStep
//	                                  nil), not EOF (ZeroReadIsEOF false for SOCK_DGRAM)
//	TestUDPRecvTruncates         U4   a 100-byte datagram into 10 bytes: (10, its first 10, sender,     measured   RecvStep (d.take n)
//	                                  nil); the rest discarded, the next read the next datagram
//	TestUDPRecvEmptyBuffer       U4   a 0-byte buffer: no shortcut (poll.FD.ReadFromInet4); blocks      measured   RecvStep (n = 0; the model does
//	                                  with nothing queued; (0, sender, nil) with one, consumed                       not consume: allows more)
//	TestUDPZeroValue             U9   zero UDPConn: ReadFromUDP (0, nil, EINVAL), WriteToUDP (0, EINVAL), measured   the models' id-0 check (net.lean)
//	                                  the bare Errno (c.ok())
//	TestUDPKilledProcess         U5,U7 a SIGKILLed child's socket with 3 datagrams queued: gone, the   measured   udp_semantics.crash, UdpLocal.init;
//	                                  address binds again, none of the 3 is received (the model                      RecvStep (over-approximates)
//	                                  allows it), a later one is
//	TestUDPNetnsFragmentation    U2,U3 MTU 1500 (veth ends, router ports, a bridge with a veth port; lo measured   intactMax, Intact
//	                                  65536): 1472 bytes one packet (Ip.FragCreates +0), intact; 1473
//	                                  (1473, nil), fragmented (FragOKs +1, FragCreates +2), not EMSGSIZE
//	                                  (IP_MTU_DISCOVER WANT, ip_no_pmtu_disc 0)
//	TestUDPNetnsFaults           U3,U5 netem loss 20%, duplicate 20%, delay 5ms 5ms, reorder 25%: of    measured   UdpGlobal.sent, RecvStep, Intact
//	                                  2000 datagrams (48-1472 bytes) some lost, some received twice,
//	                                  some out of order, every one received identical to one sent
//	TestUDPNetnsSentBeforeBind   U5   a datagram sent before the bind is dropped (Udp.NoPorts +1) and   measured   UdpGlobal.sent, RecvStep
//	                                  never received after it (the model allows it: over-approximation)
//	(the interfaces' MTU)        U3   examples/lib/robust sets no MTU: its veth pairs and bridge br0    documented intactMax (target configuration)
//	                                  have the default 1500 (as measured above), its local mode uses
//	                                  127.x (lo, 65536)
//	(no corruption)              U3   the target links (veth, loopback, bridge) copy memory, and no      assumed    Intact (prose: the deployment)
//	                                  netem corrupt is used (robust's LinkFaults has none); a real
//	                                  link's corruption would also have to pass the UDP checksum
//	(the closed world)           U5   no process but the deployment's nodes sends a datagram to an      assumed    (prose: Impl.lean, the deployment)
//	                                  address a node's socket is bound to
//	(the initial network)        U8   no datagram before the deployment's processes start              assumed    UdpGlobal.init
//	(the stutter convention)     U13  every operation may stutter (a blocked ReadFromUDP or            documented UdpStep, IsUdpStep, OrInvalid
//	                                  WriteToUDP); an invalid argument panics
//	(not modeled)                U12  Close and every other method promoted from conn (deadlines,       not modeled (no trusted model: a
//	                                  LocalAddr, RemoteAddr, SetReadBuffer, ...), DialUDP and connected               program calling one is stuck)
//	                                  Read/Write, ListenPacket, the networks "udp" and "udp6", wildcard
//	                                  and IPv6 addresses, broadcast, multicast, ReadMsgUDP/WriteMsgUDP;
//	                                  the tests' own Close and deadlines are the harness's
//
// The refutation, and the fix (2026-11-14). The first draft of D1 broke a
// direction only in a Read that returned an error. After a crash (D10) the dead
// node's directions stay open and the dead node runs no Close, so they could
// leave open only by such an error, but Linux's FIN for a dead process makes the
// peer's Read return EOF with no error before it, and a RST's error can be taken
// by the peer's Write, after which its Reads return EOF with no error
// (TestKilledWriterFin, TestKilledResetTakenByWrite, TestServerKilledBeforeReply
// refuted it). D1 now lets the connection break at any Read, keeping a prefix of
// the unread bytes, the Read answering as a Read of the broken direction does
// (bytes, EOF or an error: ReadOutcome's last clause over ReadAvail), so these
// traces are allowed.
//
// The second refutation (2026-11-14, notes/axiom-review/tcp-semantics.md).
// WriteOutcome lets a Write fail only with fewer bytes written than asked (k <
// len(bs)), so an empty Write on an end that is not closed, into a direction
// it has not shut, can only succeed; Go returns (0, err) there with an
// expired write deadline (prepareWrite runs before write(2)) or after a reset
// (write(2) of no bytes still fails: tcp_sendmsg_locked checks the socket's
// error and state first). TestEmptyWrite measures it, and
// examples/axiomcx/tcp-emptywrite is a program that panics on every run and
// had a closed no-panic theorem from the semantics (emptywrite_crash_safety).
// Fixed the same day: WriteOutcome's failures write a shorter prefix or
// nothing (k < len(bs) or k = 0), and the counterexample's proof no longer
// holds (its translation and proof were removed; the program and its test
// remain in examples/axiomcx/tcp-emptywrite). The same review found that a
// zero-value TCPConn's id 0 named connection 0's dialer end: now no
// connection or listener has id 0, so the model is stuck there (Go returns
// EINVAL), and stated the deployment the theorems assume (Impl.lean, D13:
// a closed world, addresses that do not alias, ports outside the ephemeral
// range, the target configuration).
//
// v3 (2026-11-14, notes/net-tcp-v3-plan.md): errors are Go's values (D14),
// which needs the Write/Close race (D15: with identities, a Write returning
// (k > 0, ErrClosed) is observable, and v2 allowed it only as a cut); a failed
// Dial may leave an abandoned connection (D16); Close of an open end or
// listener succeeds (D17); the addresses (D18); DialTimeout (D19, both timeout
// shapes); the plan's well-formedness as a decidable premise (D20); wildcard
// listens (D21).
//
// The third refutation (2026-11-14, the v3 review's R1). v3's Write was one
// step, and WriteOutcome let it time out only with the write deadline set at
// that step; Go's Write is a loop of write(2) calls that checks the deadline
// in each wait, so a deadline set while it blocks, after the peer read some
// of its bytes, makes it return (n, os.ErrDeadlineExceeded): excluded, since
// the bytes the peer read were appended by the Write's one step, before the
// deadline was set. TestWriteDeadlineSetDuring measures it, and
// examples/axiomcx/tcp-writedeadline panics in 99 of 100 runs and had a closed
// no-panic theorem from the semantics (writedeadline_safety). Fixed the same
// day (v3.1): the trusted conn.Write.impl is Go's loop, each write(2) with its
// wait one step of the extension's "Write" (WriteOutcome, on the bytes not yet
// written: some appended, or a failure appending nothing), so a deadline set
// or a Close made between two steps applies at the next one (D15); the
// counterexample's translation and proof were removed, its program and test
// kept.
//
// v3.2 (2026-11-15, the user's decision; D22): every operation may stutter, as
// in Perennial's Grove extension, which is how a blocked call is modeled (the
// relations' own waits went: ReadRes.wait, AcceptStep's waiting clause, a
// Write step counting nothing of a non-empty buffer), and every state has an
// outcome besides the stutter: an invalid use (Listen or Dial outside the
// plan, an id naming nothing, an argument of another shape, an unknown
// operation) panics, where v3.1 was stuck. The zero values are now modeled as
// Go has them (TestZeroValues: the models return the bare syscall.EINVAL
// before calling the extension).
//
// Also measured, the fork window (child_test.go, forkMu): while a process
// forks (os/exec), the child holds a copy of every fd until its exec, so a
// socket closed meanwhile stays open in the kernel: a closed listener's
// address refused a new Listen (EADDRINUSE) and completed a Dial that was
// then reset. All allowed (D6, D8: failure always; D9: pending stays
// pending). The tests that need a Close to take effect at once exclude forks.
//
// v3.3 (2026-11-19, phase 2 of notes/dsverify-net-port-plan.md): the network
// "tcp4" (D23), the socket options (D24), and Go's write lock (D25): before
// v3.3 two concurrent Writes of one end could interleave their steps in the
// model, which Go's fdMutex excludes (TestWriteLock); a Write's first step now
// takes the end's write lock and its last releases it, a first step waiting
// (a stutter, its only outcome) while another Write holds it.
//
// v3.4 (2026-11-20, notes/net-tcp.md, v3.4): no plan and no hosts (D6, D13,
// D20, D21). Before, the deployment's plan named each address the program may
// use and the host that may listen at it, and Listen panicked at an address
// that was not its host's (a wildcard resolving to the plan's only address
// with its port); now Listen of any valid address or wildcard (listenOk) may
// succeed on any machine, a Dial of any valid address (addrOk), and a wildcard
// listener takes connections dialed to any address with its port
// (lisAccepts). It only adds behaviors, each from a step that was a panic: a
// Listen the kernel refuses (EADDRNOTAVAIL, TestListenNotLocal; EADDRINUSE)
// is a sys failure, and which machine listens where is the proofs' business.
//
// v3.5 (2026-11-23, notes/net-sticky-read.md): a sys read error only once
// nothing is unread (D1, ReadAvail's sys clause gains d.bytes = []). Before,
// a Read could fail ECONNRESET with bytes unread and a later Read return
// them; Linux never does (the sticky tests above: an error from read(2)
// only when it copied nothing, and every sys source ends the socket's
// receiving). It only removes behaviors. So after a Read returns EOF or a
// sys error, its direction is dead (empty, not open), which no step undoes,
// and every later non-empty Read of that end returns no byte; a read
// deadline's timeout stays non-sticky (TestStickyNotTimeout).
//
// Not measured here: D12 (ENOMEM, ENOBUFS), unreachable addresses. What a
// peer sees of a machine that dies silently (nothing, then its kernel's
// timeout) is measured by the partitions of netns_test.go, as are the resets
// a middlebox injects.
package semantics
