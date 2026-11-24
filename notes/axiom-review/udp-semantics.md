# Review of the UDP extension's trusted semantics (2026-11-24)

An independent adversarial review (the `axiom` skill and Perennial's review-trusted checklist, by a
subagent given the code, not the author's conclusions) of `GooseLang/Ext/Udp/Impl.lean`, the UDP
models in `Net/TrustedCode/net.lean`, and the statements of `GooseLang/Ext/Udp/{Ghost,Specs}.lean`
and `Net/Spec/net/{ListenUDP,UDPConn__WriteToUDP,UDPConn__ReadFromUDP}.lean`. Target configuration:
Linux 7.0, Go 1.27.3. Every finding is resolved on branch `udp-net/2026-11-24`.

| # | Finding | Resolution |
|---|---|---|
| 1 | Unsound: `ReadFromUDP`'s model returned a new `*UDPAddr` on an error, where Go returns `nil` (`udpsock_posix.go`: "No sockaddr, so don't return UDPAddr"). Reachable: an unconnected socket aborted by `ss -K` returns `ECONNABORTED`; a program reading `addr.Port` then panics in Go. | The model returns `nil` on an error. |
| 2 | Refuted argument: the intactness bound was 1472 bytes, argued from the interfaces' MTU of 1500. What decides fragmentation is the path MTU, which one ICMP "fragmentation needed" message lowers (measured: a forged MTU of 552 fragmented a 1472-byte payload). | `intactMax = 524`: Linux's floor `net.ipv4.route.min_pmtu` (552) less 28 bytes of headers (`TestUDPNetnsPmtuFloor`: a forged MTU of 68 is clamped to 552; 524 bytes stay whole, 525 fragment). |
| 3 | `ListenUDP`'s error may be a bare `syscall.Errno` (`listenDatagram` returns `fd.init()`'s error unwrapped: `epoll_ctl`'s `ENOMEM`/`ENOSPC`), not only an `*os.SyscallError`. | The model allows both. The same gap exists in the TCP extension's `Listen` (reported to its owner). |
| 4 | Go's `fdMutex` panics with more than 2^20 waiters on one socket; the persistent `udpConnAt` lets a program wait on it without bound. | Documented as a known limitation, as for TCP. |
| 5 | The closed world and the target configuration left out kernel senders, NAT/`REDIRECT`/`TPROXY`, datagrams queued from an earlier run, outside processes acting on node sockets, and checksum-failed datagrams copied into the receive buffer. | Documented in the assumptions. |
| 6 | The docs cited an unfold of `Close` that the translation does not emit. | Corrected: with `UDPConn` trusted, the promoted `conn` methods have no unfold, so a call is stuck. |

Checked and held: Go's return values on every path, and `EINTR`/`EAGAIN` handling; `udpAddrOf` is
injective and canonical; `SO_BROADCAST`, and multicast excluded by `addrOk`; no ICMP errors on
unconnected sockets; no partial `sendto`; the interpretation holds only state-determined ghost state,
and a crash gives a fresh socket map; the initial states are satisfiable; `WriteToUDP.spec`'s result
depending only on success, and the persistent `udpConnAt`, are sound.

Not done: no goose run with the trusted entries moved to `translate` (they wrap system calls, which
goose cannot translate).
