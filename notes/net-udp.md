# UDP at the `net` level: the extension `udpExt`

Started 2026-11-24 (branch `udp-net/2026-11-24`; the user's decision of 2026-11-24: raft's top-level
examples are `raft_kvnet_robust` over TCP and one over UDP, which needs "more net semantics"). The
goal: a semantics of Go's `net` UDP sockets, as conservative as possible (the model may allow more
behaviours than Linux, never fewer), and the specs a raft transport over UDP needs.

## Where things are

| What | Where |
|---|---|
| the semantics (trusted) | `GooseLang/Ext/Udp/Impl.lean`: its header is the semantics in prose, decisions U1-U14 |
| the measured evidence, one Go test per decision | `examples/net/semantics/udp_*_test.go` (indexed in `doc.go`, rows `U1`...) |
| ghost state, its interpretation | `GooseLang/Ext/Udp/Ghost.lean` |
| the extension's WPs | `GooseLang/Ext/Udp/Specs.lean` |
| crash interpretation, start resources | `GooseLang/Ext/Udp/Adequacy.lean` |
| `net`'s UDP models (trusted) | `Net/TrustedCode/net.lean` (the `UDPConn` section), `Net/Code/net.toml` |
| Go-level specs and proofs | `Net/Spec/net/{ListenUDP,UDPConn__*}.lean`, `Net/Proof/net/...` |
| one Lean `example` per measured row | `GooseLang/Ext/Udp/Tests.lean` |

## Design choices (and why)

**A separate extension, not more state in `netExt`.** Perennial composes extensions as a tuple
(`ExtTuple`), each with its own local and global state, crash relation and interpretation; an
operation `ExternalOp name op` goes to the first extension of that name (`extNamed`). `udpExt` is
named `"net.udp"` (the convention, as `go.etcd.io/etcd/pkg/v3/idutil.issue`: the Go package, and a
part of it). So the TCP semantics, its specs and every proof over it are untouched: a program over
TCP alone has `[netExt, ...]`, one that also uses UDP adds `udpExt`. The two share nothing in the
kernel that a program could observe through the modeled calls (a TCP and a UDP socket may bind the
same address and port: separate port spaces).

**`UDPConn` is a trusted type of its own layout**, not Go's `struct{ conn }`: Go's `UDPConn` embeds
the same `conn` as `TCPConn`, whose trusted methods (`conn.Close`, the deadlines, ...) call the TCP
extension. A translated `UDPConn` would route `Close` to TCP's model. The model's `UDPConn` is
`struct{ uid uint64; laddr Addr; net string }` with its own trusted `WriteToUDP` and `ReadFromUDP`.
`Close` is not modeled: goose resolves the promoted `conn` methods (`Close`, the deadlines, ...)
through the embedded `conn` field, which this layout lacks, so a program calling one is stuck. A
program over UDP keeps its socket for its process's life (the kernel closes it at exit or crash,
U7). Modeling `Close` would need `conn.Close`'s TCP model to dispatch on the network: an edit of
the TCP models, left for when a program needs it.

**`Close` is an unprovable path, not a no-op and not TCP's `Close`.** With `UDPConn` trusted and
`UDPConn.Close` not listed, goose emits no unfold of the promoted `conn` methods for it
(`UDPConn.TypeAssumptions` has only `ptr_ReadFromUDP_unfold` and `ptr_WriteToUDP_unfold`; an earlier
regeneration, with `UDPConn.Close` listed as trusted, had emitted `ptr_Close_unfold` through the
embedded field, and was dropped). So a call of `Close`, `Read`, `Write`, the deadlines, `LocalAddr`
on a `*UDPConn` has no step: no WP of it can be proved, whatever the program relies on.

**The network is the datagrams sent to each address, never consumed** (as Perennial's Grove
extension, `GroveGlobalState.groveNet`, Perennial's model of a datagram network since the Rocq
version): a send adds the datagram to its destination's set; a receive returns any datagram of its
socket's address's set, and leaves it there. That one rule gives every fault UDP has: loss (a
datagram never received), duplication (received again, any number of times), reordering (any
member), delay (at any later time). No fault is a step of its own, and the state has no
history-like part a program cannot observe: the set is exactly the datagrams that may still arrive,
which in a model without time is every datagram sent (a duplicate may come arbitrarily late: netem
delays duplicates independently).

**Integrity of small datagrams; any bytes for large ones.** A datagram whose payload is at most
524 bytes (Linux's floor on a path MTU, `net.ipv4.route.min_pmtu` = 552, minus the IPv4 and UDP
headers) arrives byte for byte as sent: it is never fragmented by IP, whatever ICMP "fragmentation
needed" message lowers the path MTU (the review found that 1472, argued from the interface MTU of
1500, is refuted by one forged ICMP message), the
links of the configuration (veth, loopback) do not corrupt, and the UDP checksum (always computed
by Linux for IPv4) guards a real link. A larger datagram is fragmented by IP (or refused with
`EMSGSIZE`); fragments of distinct datagrams can be misassembled (RFC 4963), so the model lets a
large send deliver any bytes, of any length, to its destination. A program that wants integrity
sends at most 524 bytes per datagram (the raft transport's datagrams are at most 524 bytes).

**Addresses** are the TCP extension's valid strings (`addrOk`, D20: canonical IPv4 unicast
`a.b.c.d:p`, the port outside the ephemeral range), reused as they are (one audited definition). The
Go API takes a `*UDPAddr`; the model turns its `IP` (4 bytes, or 16 bytes with the IPv4 prefix, as
Go's `IP.To4`) and `Port` into that string (`udpAddrOf`; the `Zone` is ignored, as Go ignores it
for IPv4: `TestUDPListenForms`) and panics (a use the deployment excludes) unless the result is
valid.

**More than Linux, each sound:** any node may bind any valid address, and twice (Linux refuses an
address not its own, `EADDRNOTAVAIL`, and a second bind, `EADDRINUSE`; the model allows the failure
and also the success); a datagram sent before a socket was bound, or to an earlier incarnation of
the receiving node, may still be received (Linux drops it); a failed send may still have sent its
datagram; any receive may fail with a system error; the source address a receive reports is
arbitrary (the program must not trust it; the raft transport does not use it).

## Open

- Deadlines (`SetReadDeadline` on a `UDPConn`) are not modeled; added if the example needs them.


## The decisions in detail

`GooseLang/Ext/Udp/Impl.lean`'s header states the semantics briefly; this section gives each
decision with its reasons (as the header stated them until 2026-11-24, when the header was made a
concise plan). The rows `U1`... are those of `examples/net/semantics/doc.go`.

The UDP extension of GooseLang [Trusted definitions!]: the semantics of Go's `net` package's UDP
sockets (`net.ListenUDP`, `(*UDPConn).WriteToUDP`, `ReadFromUDP`), between the nodes of a
distributed system (Perennial's `DistLang.lean`). Its operations are the socket layer under those
calls; the trusted models of `net`'s UDP functions and methods (`Net/TrustedCode/net.lean`, the
`UDP` section) call them. Each decision below has a Go example measured on Linux in
`examples/net/semantics/udp_*_test.go` (indexed in its `doc.go`, rows `U1`...), and an `example` of
`GooseLang/Ext/Udp/Tests.lean` (outside the trust base) that the relations allow or exclude what
the Go example shows; `notes/net-udp.md` gives the reasons.

**Version u1** (2026-11-24).

**An extension of its own.** `udpExt` (named `"net.udp"`: the Go package `net`, its UDP part) is
separate from the TCP extension `netExt` (`GooseLang/Ext/Net/Impl.lean`): its own local and global
state, crash relation and ghost state. A program over TCP and UDP has both in its list of
extensions. It reuses the TCP extension's definitions that mean the same here: the valid addresses
(`Net.addrOk`, D20), the error kinds (`Net.NetErr`, D14) and their codes (`Net.errCode`,
`Net.failV`). TCP and UDP ports are separate spaces in the kernel, so nothing one extension does is
visible to the other's operations.

**State: only what a program can observe.** The global state (`UdpGlobal`) is, for each address,
the datagrams sent to it (`sent`, any order, a datagram as many times as it was sent): exactly the
datagrams that may still be delivered there, since a duplicate may arrive at any later time (the
model has no time). A node's local state (`UdpLocal`) is its sockets, each the address it is bound
to (a socket is never closed but by its process's end: `Close` is not modeled, U12). **Initial states**: no socket; no datagram.

**Faults come from one rule (U5): a receive returns any datagram sent to its address, and leaves
it there** (as Perennial's Grove extension, `GroveGlobalState.groveNet`). So a datagram may be lost
(never received), duplicated (received again, any number of times, by one socket or several),
reordered (any of them first), delayed (received at any later step). No fault is a step of its own.

**Handles.** A socket is named by a 64-bit id of its node, never 0 (`ListenStep`); an operation on
an id that names no socket of the node panics (U13). The trusted models pass only ids the
extension returned, which a Go program cannot forge (inside `net`'s unexported fields, and the heap
does not survive a crash); a zero-value `UDPConn` holds the id 0, and the models check for it before
calling the extension, returning Go's `syscall.EINVAL` as Go's methods do (`c.ok()`).

**Addresses (U1).** The Go calls take a `*UDPAddr`; the models pass its `IP` and `Port` to the
extension, which turns them into the canonical string (`udpAddrOf`: an `IP` of 4 bytes, or of 16
bytes starting with the IPv4-mapped prefix `::ffff:0:0/96`, as Go's `IP.To4`; a port in
`0..65535`; the `Zone` is ignored for IPv4, as Go's `ipToSockaddrInet4`) and requires it to be a
valid address (`Net.addrOk`, D20: canonical IPv4 unicast, the port nonzero and outside the
ephemeral range). Any other address panics (U13): a use the deployment excludes (D13).

* U1 `"Listen"` of `(ip, port)` (Go's `ListenUDP("udp4", laddr)`): a new open socket bound to the
  address `a`; or a `sys` failure (`EADDRINUSE`, `EADDRNOTAVAIL`). Any node may bind any valid
  address, and more than once: more than Linux, which refuses an address that is not the
  machine's and a second bind of an address (Go sets no `SO_REUSEADDR` or `SO_REUSEPORT` on a
  unicast UDP socket); each refusal is a failure the model allows.
* U2 `"Send"` of the bytes `bs` from the socket `s` to `(ip, port)` (Go's `WriteToUDP`, one
  `sendto(2)`, waiting while the socket's buffer is full): one datagram `d` with `Intact bs d` is added to the destination's datagrams and
  the send succeeds; or it fails with `sys` (`EMSGSIZE`, `ENOBUFS`, `EPERM`, ...), and `d` is added
  or not (a failure need not mean nothing was sent: more than Linux). Until then it waits (a
  stutter). A send to an address no socket is bound to succeeds as any other (Linux sends it and
  the destination drops it; an ICMP error is not reported to an unconnected socket, and would be a
  `sys` failure, which the model allows anyway).
* U3 `Intact bs d` (integrity): a payload of at most `intactMax = 524` bytes is delivered byte for
  byte (`d = bs`); a larger one may be delivered as any bytes. Why: what decides IP fragmentation is
  the path MTU, which an ICMP "fragmentation needed" message (from anywhere: no closed-world
  assumption excludes it) can lower, but never below Linux's floor `net.ipv4.route.min_pmtu`, 552 by
  default (a smaller MTU is clamped to it, `mtu lock 552`); 524 is 552 less the IPv4 (20) and UDP (8)
  headers, so such a datagram is one IP packet, never fragmented, whatever ICMP arrives
  (`TestUDPNetnsPmtuFloor`: a forged MTU of 68 leaves 524 bytes whole and fragments 525). The links
  do not corrupt a packet (veth and loopback copy memory; no `netem corrupt`), and Linux always
  computes the UDP checksum of an IPv4 datagram, which a real link's corruption would have to pass.
  A larger datagram may be fragmented by IP (at the interface MTU, 1500 in the target
  configuration, or at a path MTU an ICMP message lowered; or refused, `EMSGSIZE`), and fragments of
  distinct datagrams with one IP id may be reassembled together (RFC 4963), with a checksum that
  matches with probability 2^-16: so any bytes, of any length. (Until the review of 2026-11-24 this
  was 1472, argued from the interface MTU alone: refuted by a forged ICMP message, the review's
  finding 2.)
* U4 `"Recv"` of at most `n` bytes at the socket `s` (Go's `ReadFromUDP(b)`, `n = len(b)`, one
  `recvfrom(2)`): the first `min n |d|` bytes of a datagram
  `d` sent to the socket's address (Linux copies what fits and discards the rest of the datagram;
  Go returns the count copied and no error); or a `sys` failure (more than Linux for an unbound,
  unconnected socket); until then it waits (a stutter). The source address Go returns is not
  modeled here: the trusted model returns a new `*UDPAddr` with arbitrary fields (U10).
* U5 the faults (above): loss, duplication, reordering, delay; and more than Linux: a datagram sent
  before the destination socket was bound, or while its node was down, or to an earlier
  incarnation of the node, may still be received (Linux drops one that arrives where no socket is
  bound; the model has no time to tell them apart).
* U7 crash (a node's crash or its process's exit): the node's sockets are gone (the kernel closes
  them); the network's datagrams stay (a datagram in flight or queued at a live receiver may still
  arrive).
* U8 initial states: no socket on a node (`UdpLocal.init`), no datagram in the network
  (`UdpGlobal.init`).
* U9 errors: every failure is D14's kind `sys`, a system call's error (an `*os.SyscallError` with
  an arbitrary nonzero `Errno`), wrapped by the models in Go's `*OpError`
  (`Net/TrustedCode/net.lean`). The kinds `closed` and `timeout` cannot occur: no socket is closed
  and no deadline set (U12).
* `"AnyBool"`, `"AnyString"`, `"AnyW64"`, `"AnyErrno"`: an arbitrary value; for `"AnyErrno"` a
  nonzero word (the parts of an error and of an address the model does not explain).
* U13 **Steps: every operation may stutter, which is how waiting is modeled; invalid uses panic**
  (`UdpStep`, as the TCP extension's D22 and Perennial's Grove extension): any call may take a step
  that changes nothing and leaves the call as it was; every state has an outcome besides the
  stutter, a panic (GooseLang's stuck builtin `Panic`) when the argument is one the extension
  cannot use: an invalid address (U1), an id naming no socket of the node, another argument shape,
  an unknown operation.

**The deployment** (D13 of the TCP extension, for UDP). *Valid addresses* as above. *A closed
world* (stated in prose only): no sender other than the deployment's nodes (no process and no kernel
sender: netconsole, a UDP tunnel), on any machine, sends a datagram to an address a node's socket is
bound to (an outside sender would add datagrams no node sent), and none was sent before the
deployment started (nothing queued in a qdisc from an earlier run with the same addresses); no
packet filter or routing rule rewrites a datagram's destination (NAT, `REDIRECT`, `TPROXY`, policy
routing), so delivery is by the destination address as sent; no process outside the deployment acts
on a node's sockets (`ss -K`, `pidfd_getfd`: their effects are `sys` failures, which the model
allows anyway). *The target configuration*: Linux 7.0 with its default sysctls (among them
`net.ipv4.route.min_pmtu` = 552, U3), no `netem corrupt`, Go 1.27.3, measured in
`examples/net/semantics/`. The no-corruption assumption also covers the bytes of the receive buffer
beyond the count a receive returns: Linux's `udp_recvmsg` copies a datagram whose checksum fails into
the buffer before dropping it and retrying (`csum_copy_err`), which the specs' "the rest of `b` is
unchanged" would not survive; with no corruption no checksum fails.

**Known limitation** (as the TCP extension's, the review's finding 4): Go's `fdMutex` panics ("too
many concurrent operations on a single file or socket") when more than 1048575 calls wait for one
socket's read or write lock; the model lets them wait. A program with more than 2^20 goroutines
blocked on one socket can panic in Go where the model says it cannot.

**What is not modeled** (U12): `Close` and every other method of `conn` promoted to `*UDPConn`
(the translation has no unfold of them for the trusted `UDPConn`, `UDPConn.TypeAssumptions` lists
only `ReadFromUDP` and `WriteToUDP`, so a call is stuck; Go's `Close`, which a program over UDP need
not call: its process's end closes the socket, U7), deadlines on a `UDPConn`, connected UDP sockets (`DialUDP`, `Read`,
`Write`), `ListenPacket`, wildcard and IPv6 addresses, the networks `"udp"` and `"udp6"`,
broadcast, multicast, `ReadMsgUDP`/`WriteMsgUDP`, socket options and buffer sizes, `LocalAddr`,
`RemoteAddr`. Their methods have no model, so a program calling one is stuck (no proof).
