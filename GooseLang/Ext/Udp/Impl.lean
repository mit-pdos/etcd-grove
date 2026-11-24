/-
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
-/
module

public import GooseLang.Ext.Net.Impl

@[expose] public section

namespace Perennial

namespace Udp

open Net

/-- The network: the datagrams sent to each address (an address with none has no entry). -/
structure UdpGlobal where
  sent : GMap GoString (List (List w8))

instance : Inhabited UdpGlobal := ⟨⟨∅⟩⟩

/-- The datagrams sent to `a`. -/
def UdpGlobal.sentTo (g : UdpGlobal) (a : GoString) : List (List w8) :=
  (g.sent !! a).getD []

/-- The network with `d` added to the datagrams sent to `a`. -/
def UdpGlobal.add (g : UdpGlobal) (a : GoString) (d : List w8) : UdpGlobal :=
  { g with sent := g.sent.insert a (d :: g.sentTo a) }

/-- A node's state: its sockets, each the address it is bound to. -/
structure UdpLocal where
  socks : GMap w64 GoString

instance : Inhabited UdpLocal := ⟨⟨∅⟩⟩

/-- U8. A machine's initial state: no socket. -/
def UdpLocal.init (L : UdpLocal) : Prop := L.socks = ∅

/-- U8. The network's initial state: no datagram. -/
def UdpGlobal.init (g : UdpGlobal) : Prop := g.sent = ∅

/-- The UDP extension. -/
@[reducible] def udpExt : GooseExt where
  name := "net.udp"
  Val := Empty
  LocalState := UdpLocal
  GlobalState := UdpGlobal

/-! ## Addresses (U1) -/

/-- The decimal digits of `n`, most significant first, with no leading zero (`"0"` for 0). -/
def decDigits (n : Nat) : GoString :=
  if h : n < 10 then [BitVec.ofNat 8 (48 + n)]
  else decDigits (n / 10) ++ [BitVec.ofNat 8 (48 + n % 10)]
termination_by n
decreasing_by omega

/-- The IPv4-mapped prefix of a 16-byte IP, `::ffff:0:0/96` (Go's `v4InV6Prefix`). -/
def v4InV6Prefix : List w8 := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xff]

/-- The four bytes of an IPv4 address held in a Go `IP` (Go's `IP.To4`): 4 bytes, or 16 starting
with the IPv4-mapped prefix. -/
def ipv4Of (ip : List w8) : Option (List w8) :=
  if ip.length = 4 then some ip
  else if ip.length = 16 ∧ ip.take 12 = v4InV6Prefix then some (ip.drop 12)
  else none

/-- U1. The canonical string `a.b.c.d:p` of the IP `ip` and the port `port` (a Go `int`, as a
64-bit word), if `ip` holds an IPv4 address and `port` is in `0..65535`. -/
def udpAddrOf (ip : List w8) (port : w64) : Option GoString :=
  match ipv4Of ip with
  | some [b1, b2, b3, b4] =>
    if port.toNat ≤ 65535 then
      some (decDigits b1.toNat ++ [46] ++ decDigits b2.toNat ++ [46] ++ decDigits b3.toNat ++
        [46] ++ decDigits b4.toNat ++ [58] ++ decDigits port.toNat)
    else none
  | _ => none

/-- U1. `(ip, port)` is a valid address, `a`. -/
def ValidDest (ip : List w8) (port : w64) (a : GoString) : Prop :=
  udpAddrOf ip port = some a ∧ addrOk a = true

/-! ## Outcomes -/

/-- U3. The payload at most this long is delivered intact. -/
def intactMax : Nat := 524

/-- U3. A datagram `d` the network may deliver for a send of the bytes `bs`. -/
def Intact (bs d : List w8) : Prop := bs.length ≤ intactMax → d = bs

section step
variable [GooseExts] [GoGlobalContext]

/-- U1. `"Listen"` at the valid address `a` by the node with state `L`. -/
def ListenStep (a : GoString) (L : UdpLocal) (e' : Expr) (L' : UdpLocal) : Prop :=
  (e' = Val (failV .sys) ∧ L' = L) ∨
  (∃ s, s ≠ 0 ∧ L.socks !! s = none ∧
    e' = Val (PairV (#s) (#(W64 0))) ∧ L' = { L with socks := L.socks.insert s a })

/-- U2, U3. `"Send"` of `bs` to the address `a`. -/
def SendStep (bs : List w8) (a : GoString) (g : UdpGlobal) (e' : Expr) (g' : UdpGlobal) : Prop :=
  ∃ d, Intact bs d ∧
    ((e' = Val (#(errCode none)) ∧ g' = g.add a d) ∨
     (e' = Val (#(errCode (some .sys))) ∧ (g' = g.add a d ∨ g' = g)))

/-- The value of a receive's result: the bytes and the code (`0` success, `NetErr.code` an
error). -/
def recvRes (bs : List w8) (code : w64) : val := PairV (#bs) (#code)

/-- U4, U5. `"Recv"` of at most `n` bytes at a socket bound to `a`. -/
def RecvStep (a : GoString) (n : w64) (g : UdpGlobal) (e' : Expr) : Prop :=
  e' = Val (recvRes [] (errCode (some .sys))) ∨
  ∃ d ∈ g.sentTo a, e' = Val (recvRes (d.take n.toNat) (errCode none))

/-- U13. An invalid use: a panic (GooseLang's builtin one, stuck: `wp_PanicOp`), nothing
changed. -/
def Invalid (L : UdpLocal) (g : UdpGlobal) (e' : Expr) (L' : UdpLocal) (g' : UdpGlobal) : Prop :=
  e' = Panic "net.udp: invalid use of the UDP extension" ∧ L' = L ∧ g' = g

/-- U13. An operation whose argument is valid when `valid` holds: its `step`, or, if `valid` does
not hold, a panic. -/
def OrInvalid (valid step : Prop) (L : UdpLocal) (g : UdpGlobal) (e' : Expr) (L' : UdpLocal)
    (g' : UdpGlobal) : Prop :=
  step ∨ (¬ valid ∧ Invalid L g e' L' g')

/-- The outcome rules of the UDP extension (all but the stutter), for a node with local state `L`
on the network `g`: each operation's step on a valid argument, else a panic (U13). -/
def IsUdpStep (op : String) (v : val) (L : UdpLocal) (g : UdpGlobal) (e' : Expr) (L' : UdpLocal)
    (g' : UdpGlobal) : Prop :=
  match op with
  | "Listen" => OrInvalid
      (∃ (ip : List w8) (port : w64) (a : GoString), v = PairV (#ip) (#port) ∧ ValidDest ip port a)
      (∃ (ip : List w8) (port : w64) (a : GoString), v = PairV (#ip) (#port) ∧
        ValidDest ip port a ∧ ListenStep a L e' L' ∧ g' = g) L g e' L' g'
  | "Send" => OrInvalid
      (∃ (s : w64) (bs ip : List w8) (port : w64) (la a : GoString),
        v = PairV (#s) (PairV (#bs) (PairV (#ip) (#port))) ∧ L.socks !! s = some la ∧
        ValidDest ip port a)
      (∃ (s : w64) (bs ip : List w8) (port : w64) (la a : GoString),
        v = PairV (#s) (PairV (#bs) (PairV (#ip) (#port))) ∧ L.socks !! s = some la ∧
        ValidDest ip port a ∧ SendStep bs a g e' g' ∧ L' = L) L g e' L' g'
  | "Recv" => OrInvalid
      (∃ (s n : w64) (a : GoString), v = PairV (#s) (#n) ∧ L.socks !! s = some a)
      (∃ (s n : w64) (a : GoString), v = PairV (#s) (#n) ∧
        L.socks !! s = some a ∧ RecvStep a n g e' ∧ L' = L ∧ g' = g) L g e' L' g'
  | "AnyBool" => OrInvalid (v = #())
      (v = #() ∧ (∃ b : Bool, e' = Val (#b)) ∧ L' = L ∧ g' = g) L g e' L' g'
  | "AnyString" => OrInvalid (v = #())
      (v = #() ∧ (∃ str : GoString, e' = Val (#str)) ∧ L' = L ∧ g' = g) L g e' L' g'
  | "AnyW64" => OrInvalid (v = #())
      (v = #() ∧ (∃ n : w64, e' = Val (#n)) ∧ L' = L ∧ g' = g) L g e' L' g'
  | "AnyErrno" => OrInvalid (v = #())
      (v = #() ∧ (∃ n : w64, n ≠ 0 ∧ e' = Val (#n)) ∧ L' = L ∧ g' = g) L g e' L' g'
  | _ => Invalid L g e' L' g'

/-- The step relation of the UDP extension, for a node with local state `L` on the network `g`
(U13): the operation stutters (nothing changes, the call stays as it was), or it takes one of its
outcome rules (`IsUdpStep`). The heap does not change. -/
def UdpStep (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (L : UdpLocal) (g : UdpGlobal)
    (e' : Expr) (h' : GMap Loc (NonAtomic val)) (L' : UdpLocal) (g' : UdpGlobal) : Prop :=
  h' = h ∧ ((e' = ExternalOp udpExt.name op (Val v) ∧ L' = L ∧ g' = g) ∨
    IsUdpStep op v L g e' L' g')

end step

/-- U7. A crash drops the sockets; U8, the initial states. -/
instance udp_semantics : ExtSemantics udpExt where
  step := UdpStep
  crash L L' := L' = { L with socks := ∅ }
  initLocal L _ := L.init
  initGlobal g := g.init

/-- A crash leaves a machine in an initial state. -/
theorem crash_init (L L' : UdpLocal) (h : udp_semantics.crash L L') : L'.init := by
  subst h; rfl

/-- The initial states are inhabited. -/
example : UdpLocal.init ⟨∅⟩ := rfl
example : UdpGlobal.init ⟨∅⟩ := rfl

end Udp

end Perennial
