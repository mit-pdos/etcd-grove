/-
The UDP extension of GooseLang [Trusted definitions!]: the semantics of Go's UDP sockets
(`net.ListenUDP("udp4", …)`, `(*UDPConn).WriteToUDP`, `(*UDPConn).ReadFromUDP`) for distributed
programs (Perennial's `DistLang`). The trusted models of those calls (`Net/TrustedCode/net.lean`,
section "UDP") are written with the operations below.

**Approach.** The network holds, for each address, every datagram sent to it. A send adds a
datagram; a receive returns any datagram sent to its socket's address and leaves it there. Loss,
duplication, reordering and delay all follow from this one rule: no fault is a step of its own. The
extension is separate from the TCP extension (`GooseLang/Ext/Net/Impl.lean`) and reuses its valid
addresses (`Net.addrOk`) and error codes (`Net.NetErr`, `Net.errCode`).

**State, initial states, crash.**
* Global (`UdpGlobal`): for each address, the datagrams sent to it.
* Local (`UdpLocal`): the node's sockets, each with the address it is bound to.
* Initially no datagram and no socket (`UdpGlobal.init`, `UdpLocal.init`).
* A crash drops the node's sockets; the datagrams stay in the network.

**Operations.** Each may also stutter, which models waiting. An argument the extension cannot use
panics (U13): an invalid address, an id naming no socket of the node, another argument shape, an
unknown operation.
* U1 `Listen (ip, port)`, with `udpAddrOf ip port` a valid address `a`: a new socket bound to `a`,
  or a `sys` failure.
* U2 `Send (s, bs, ip, port)`, to a valid address: a datagram `d` with `Intact bs d` is added to
  the destination's datagrams and the send succeeds; or it fails with `sys`, `d` added or not.
* U4 `Recv (s, n)`: the first `min n |d|` bytes of any datagram `d` sent to `s`'s address, or a
  `sys` failure.
* `AnyBool`, `AnyString`, `AnyW64`, `AnyErrno`: an arbitrary value (nonzero for `AnyErrno`), for
  the parts of errors and addresses the model leaves unspecified.

**Intactness (U3).** A payload of at most `intactMax = 524` bytes arrives exactly as sent; a longer
one may arrive as any bytes. 524 is Linux's minimum path MTU (`net.ipv4.route.min_pmtu`, 552) less
the IPv4 and UDP headers, so such a datagram is never IP-fragmented, whatever ICMP messages arrive.

**Assumptions** (stated in prose; every theorem over the extension relies on them).
* Closed world: only the deployment's nodes send datagrams to a node's address (no other process or
  kernel sender, and none left from an earlier run); no NAT, redirect or routing rule rewrites a
  destination; no process outside the deployment acts on a node's sockets.
* Target configuration: Linux 7.0 with its default sysctls, no `netem corrupt`, Go 1.27.3.
* Not modeled (U12): `Close` and the other `conn` methods promoted to `*UDPConn`, deadlines,
  connected sockets, and networks or addresses other than `"udp4"` IPv4 unicast; a call to one is
  stuck. Go panics with more than 2^20 calls waiting on one socket; the model lets them wait.

**Evidence.** Each decision has a Go test measured on the target configuration, indexed in
`examples/net/semantics/doc.go` (rows U1–U13), and a Lean example in `GooseLang/Ext/Udp/Tests.lean`.
The rationale is in `notes/net-udp.md`.
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
