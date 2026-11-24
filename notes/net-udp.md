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

**`Close` is an unprovable path, not a no-op and not TCP's `Close`.** Goose emits
`UDPConn.TypeAssumptions.ptr_Close_unfold`: `(*UDPConn).Close` is `λ r. MethodResolve (*conn)
"Close" (StructFieldRef UDPConn.ty "conn" r)` (Go's promotion through the embedded field). The
`StructFieldRef` steps to the address `structFieldRef UDPConn "conn" c`, which the semantics leaves
uninterpreted: `UDPConn` is not a plain type (it holds an interface and a string), so no offset
axiom (`structFieldRef_plain`, `Perennial/Golang/Defn/Plain.lean`) applies, and the typed points-to
of the trusted layout covers only its fields `uid`, `laddr`, `net`. TCP's `conn.Close.impl` then
starts with a load of `id` at `structFieldRef conn "id"` of that address, for which no proof can own
a points-to (the theorems hold for every interpretation of `structFieldRef`). So a WP of a `Close`
call cannot be proved: a program over UDP that calls `Close` has no proof, whatever it relies on.
The same holds for every other promoted `conn` method (`Read`, `Write`, the deadlines,
`LocalAddr`, ...).

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
1472 bytes (an MTU of 1500, minus the IPv4 and UDP headers) arrives byte for byte as sent: it is
never fragmented by IP on the target configuration (every interface's MTU is at least 1500), the
links of the configuration (veth, loopback) do not corrupt, and the UDP checksum (always computed
by Linux for IPv4) guards a real link. A larger datagram is fragmented by IP (or refused with
`EMSGSIZE`); fragments of distinct datagrams can be misassembled (RFC 4963), so the model lets a
large send deliver any bytes, of any length, to its destination. A program that wants integrity
sends at most 1472 bytes per datagram (the raft transport sends fragments of at most 1200).

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
