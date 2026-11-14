// Package semantics measures, by tests over real TCP, each decision of the TCP
// extension's trusted semantics (GooseLang/Ext/Tcp/Impl.lean: the steps
// ReadStep, WriteStep, CloseStep, CloseWriteStep, SetDeadlineStep, ListenStep,
// AcceptStep, DialStep, LisClose and the node crash; each operation's outcome
// is a relation there: ReadOutcome, WriteOutcome, CloseOutcome,
// CloseWriteOutcome, DeadlineOutcome), numbered D1-D12 as in Impl.lean's
// header:
//
//	D1  ReadStep         D5  SetDeadlineStep  D9   LisClose
//	D2  WriteStep        D6  ListenStep       D10  crash (a node's listeners go; connections untouched)
//	D3  CloseStep        D7  AcceptStep       D11  process exit: as a crash, for the peers
//	D4  CloseWriteStep   D8  DialStep         D12  not modeled (ENOMEM/ENOBUFS, other addresses, ...)
//
// Each test is one behavior: its doc comment says the decision it supports or
// refutes, what Linux and Go do, and why (the kernel or Go code path). Every
// outcome is measured: Go 1.27.3 (linux/amd64), Linux 7.0.0-38-generic, over
// 127.0.0.1 with kernel-chosen ports, the tests in parallel (go test
// -count=100 passed). Where the kernel's timing matters, a test waits
// (bounded) on a probe that changes nothing (the TCP state from TCP_INFO, the
// unread count from SIOCINQ: helpers_test.go), never on a sleep. The process
// tests re-run the test binary as a child (child_test.go) and kill it with
// SIGKILL, or let it exit.
//
// The rule (CLAUDE.md): every change to the trusted semantics adds or updates
// the test of the decision it changes, in the same commit.
//
// Index (decision; what it establishes; outcome; evidence):
//
// Reads (read_test.go):
//
//	TestReadPartial              D1   a Read returns what arrived (k <= min(n, unread)), the rest stays   allowed, measured
//	TestReadEmptyBuffer          D1   empty Read: 0, nil at once, even with bytes, an expired deadline   allowed, measured
//	                                  or a pending RST (not consumed); ErrClosed after own Close
//	TestReadEOFAfterFin          D1,D3 the bytes, then EOF, then EOF again                               allowed, measured
//
// Resets (reset_test.go):
//
//	TestResetCloseUnreadInput    D1,D3 Close with unread input sends RST; the peer reads the bytes       allowed, measured
//	                                  it had received, then ECONNRESET, then EOF
//	TestResetLingerZero          D1   SetLinger(0)+Close: the same                                       allowed, measured
//	TestResetErrorTakenByWrite   D1,D2 the reset error goes to the first call: a Write takes it, then   allowed, measured
//	                                  the reads are the bytes then EOF, no error (peer Closed: d fin)
//	TestWriteAfterPeerClose      D2   a Write after the peer's FIN succeeds, bytes lost; after the RST  allowed, measured
//	                                  every Write fails (EPIPE: RST in CLOSE_WAIT); the Read is EOF
//	TestPartialWriteOnReset      D2   a Write cut by a RST returns 0 < n < len, ECONNRESET               allowed, measured
//
// Close, CloseWrite (close_test.go):
//
//	TestCloseTwice               D1-D5 Close: nil, FIN; after it every operation errs, net.ErrClosed     allowed, measured
//	TestCloseUnblocksRead        D1,D3 own Close wakes a blocked Read with ErrClosed                     allowed, measured
//	TestCloseAfterReset          D3,D5 Close and SetDeadline of a reset end: nil                         allowed, measured
//	TestCloseWrite               D1,D2,D4 peer reads the bytes then EOF; own Write: EPIPE; own Read     allowed, measured
//	                                  still works; CloseWrite again: nil, then ENOTCONN after both FINs
//	TestCloseWriteAfterReset     D4   CloseWrite of a reset end: ENOTCONN, the reset error kept          allowed, measured
//
// Deadlines (deadline_test.go):
//
//	TestReadDeadlineLosesNothing D1,D5 a timeout consumes no byte (expired: timeout even with bytes);   allowed, measured
//	                                  time.Time{} clears it
//	TestWriteDeadlinePrefix      D2,D5 a Write past its deadline: 0 < n < len, timeout; exactly n bytes allowed, measured
//	                                  reach the peer, the connection stays usable
//
// Listeners, Dial (listen_test.go):
//
//	TestListenTwice              D6   EADDRINUSE at an open listener's address; success after its Close allowed, measured
//	TestListenTakenByOtherProcess D6  another process's listener: EADDRINUSE too (the model also allows  allowed, measured
//	                                  success: more than Linux)
//	TestDialRefused              D8   no listener: ECONNREFUSED                                          allowed, measured
//	TestAcceptAfterListenerClose D7,D9 LisClose: nil, wakes Accept with ErrClosed; Accept and Close     allowed, measured
//	                                  after it: ErrClosed
//	TestPendingAtListenerClose   D7-D9 a dialed, unaccepted connection is reset by the listener's Close; allowed, measured
//	                                  a new listener does not get it (Linux excludes what D7 allows)
//
// Process death (process_test.go):
//
//	TestKilledWriterFin          D1,D10,D11 the bytes, then EOF, no error (kernel FIN)                   allowed (D1's break), measured
//	TestKilledWithUnreadInput    D1,D10,D11 the bytes, then ECONNRESET, then EOF (kernel RST)            allowed, measured
//	TestKilledResetTakenByWrite  D1,D2,D10 Write takes the RST's error; reads: bytes then EOF, no error  allowed (D1's break), measured
//	TestWriteToKilledPeer        D2,D10 a Write after the FIN succeeds (lost); after the RST: EPIPE      allowed, measured
//	TestServerKilledBeforeReply  D1,D10,D11 the client reads EOF, no bytes, no error                     allowed (D1's break), measured
//	TestKilledListener           D7,D8,D10 the queued connection is reset; Dial then refused             allowed, measured
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
// Also measured, the fork window (child_test.go, forkMu): while a process
// forks (os/exec), the child holds a copy of every fd until its exec, so a
// socket closed meanwhile stays open in the kernel: a closed listener's
// address refused a new Listen (EADDRINUSE) and completed a Dial that was
// then reset. All allowed (D6, D8: failure always; D9: pending stays
// pending). The tests that need a Close to take effect at once exclude forks.
//
// Not measured: D12 (ENOMEM, ENOBUFS), a machine crash ("nothing": no FIN or
// RST until the peer's timeout), unreachable addresses and Dial timeouts.
package semantics
