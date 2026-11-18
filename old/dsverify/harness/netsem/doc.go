// Package netsem explains, by small Go programs, each decision of the TCP extension's trusted
// semantics (harness/lean/Harness/GooseLang/Ext/NetConn/Impl.lean) and of the trusted model of
// `net` over it (harness/lean/Harness/TrustedCode/net.lean).
//
// Each file is one decision: its doc comment says what the model does, the Lean names that
// encode it, the outcome it allows or excludes, and the evidence (measured, documented with a
// citation, or assumed). No Goose translation or proof covers this package. run.sh runs the
// measured examples on this host and prints what each observed; a change to the semantics
// updates its example in the same commit.
//
// Claimed configuration: Linux 7.0 (7.0.0-1014-aws) TCP over IPv4 (measured here on loopback,
// in a private network namespace, and over the rig's veth links: the two ends in two of the
// rig's namespaces, 10.77.0.10 and 10.77.0.11 on veth pairs into a bridge, run-veth.sh),
// Go 1.27.3's net (linux/amd64), network "tcp", addresses spelled "IP:port" identically by a
// listener and its dialers, one IP per node (AddressSpelling in documented.go).
//
// Results (run.sh, 2026-11-13; loopback, then the same over veth where it differs):
//
//	short_read.go             Read returns 1..len(buf) of the next bytes   measured: 5 ("hello"), then 3 of 5 into a 3-byte buffer, then 2
//	partial_write.go          short Write only with an error               measured: 2633835 of 67108864 bytes, timeout; the peer read exactly 2633835, then EOF
//	                                                                       veth: 796400, timeout; the peer read exactly 796400, then EOF
//	write_close_race.go       a Write stopped by its end's Close: k, closed measured (2026-11-14): 2633835 of 67108864 bytes, use of closed network connection;
//	                                                                       the peer read exactly 2633835, then EOF; veth: 796400, the same
//	write_break_partial.go    a Write stopped by a break: k, error         measured (2026-11-14): 3586419 of 67108864 bytes, ECONNRESET, after the peer had read
//	                                                                       1112286 of them (then its abortive Close); veth: 2174280, ECONNRESET, peer read 1085200
//	deadline_usable.go        a deadline times out; the conn stays usable  measured: timeout; timeout with data buffered and a past deadline; after clearing, "late"
//	close_then_eof.go         peer's Close: the rest, then EOF forever     measured: 3 bytes, then EOF EOF EOF; own closed end: "use of closed network connection"
//	break_suffix.go           a break loses a suffix; error, then EOF      measured (abortive close): 2633835 written, 127973 read, then ECONNRESET, EOF, EOF
//	                                                                       veth: 796400 written, 125336 read, then ECONNRESET, EOF, EOF
//	break_netns_test.go       the same, reset made by iptables             measured (private netns): 127973 read, then ECONNRESET, EOF, EOF; the dialer's 3 later Writes succeed (lost)
//	                                                                       veth (iptables in the acceptor's namespace): 125336 read, then ECONNRESET, EOF, EOF; 3 later Writes succeed
//	write_after_peer_close.go Write after the peer's Close: ok, then EPIPE measured: nil, broken pipe, broken pipe
//	close_unread_resets.go    Close with unread input resets               measured: the peer read the 17 bytes, then ECONNRESET, EOF, EOF
//	dial_listen.go            Dial/Listen failures; pending conns reset    measured: second Listen EADDRINUSE; Dial without Accept ok, its Read after the listener's Close ECONNRESET; then Dial ECONNREFUSED
//	dial_timeout_accepted.go  a failed Dial's connection is accepted       measured (2026-11-14): 5000 DialTimeouts of 1..60 us: 3078 ok, 1922 failed; 4889 accepted:
//	                                                                       3078 read the dialer's byte, 1811 (from failed Dials) read EOF; none carried data
//	                                                                       veth: 2693 ok, 2307 failed; 4793 accepted, 2100 from failed Dials, all EOF
//	zero_read.go              Read(empty) is (0, nil)                      measured: 0 nil after the peer's Close
//	err_closed.go             errors.Is net.ErrClosed iff own closed end   measured: true (Timeout/Temporary false/false) for Read, Write, SetDeadline, Close on a closed conn,
//	                                                                       a blocked Read closed by another goroutine, Accept and Close on a closed listener, a blocked Accept;
//	                                                                       false for io.EOF, i/o timeout, ECONNRESET, EADDRINUSE, ECONNREFUSED
//	veth_test.go              AcceptAnyOrder                               measured (veth, 1000 trials each): Dial from node 0 (netem delay 5 ms) returned, then Dial from node 2:
//	                                                                       1000 of 1000 accepted node 2's first; concurrent dials: 87, 71, 157 (with jitter) of 1000
//	                                                                       out of Dial-return order; back to back from one node: 0 of 1000
//	veth_test.go              TimeoutOnBreak                               measured (veth, partition): "connection timed out" after 2.3 s (TCP_USER_TIMEOUT 2 s), 3.1 s
//	                                                                       (keep-alive 1 s/1 s/2), 3.2 s (tcp_retries2=3): ETIMEDOUT, Timeout() true, Temporary() true,
//	                                                                       not os.ErrDeadlineExceeded; then Read EOF, EOF, Write EPIPE, EPIPE; the peer, after the partition
//	                                                                       is lifted: Write nil, then 0 bytes, ECONNRESET, EOF, EOF
//	node_identity_netns_test.go NodeIdentity (2026-11-14, private netns, one IP 10.77.0.10 on a dummy link): Listen(":p"), ("0.0.0.0:p"),
//	                          ("[::]:p") ok (Addr [::]:p), reached by Dial("10.77.0.10:p"); then Listen("10.77.0.10:p") and the other
//	                          wildcard spellings EADDRINUSE; a wildcard after Listen("10.77.0.10:p") EADDRINUSE;
//	                          Listen("10.77.0.11:p") (another node's IP) EADDRNOTAVAIL
//	documented.go             ReadShape                                    documented (Go and Linux sources cited there)
//	                          AddressSpelling, InOrderOnce                 assumed (the configuration; TCP's guarantees)
//
// Over veth every example has the same qualitative outcome as on loopback; only byte counts that
// depend on buffer sizes differ.
package netsem
