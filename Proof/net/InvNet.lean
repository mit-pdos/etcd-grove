/-
**The network's addresses, for a server's listener** (item 4, the server start; Lean-first, no
Rocq counterpart). Perennial has no network model; these two axiomatized predicates are the
vocabulary of `net.Listen`'s trust-boundary spec (`Spec/net/Listen.lean`) and of grpc's server
start (`Proof/google_golang_org/grpc/InvGrpcServer.lean`).

* `netAddrFree addr` (exclusive): no listener of this program or of any other process is, or
  will be (other than through this token), bound at the address `addr`, and (2026-11-14, the
  network fault review; reworded after the independent review) no other process connects to it,
  and the program's own connections to it carry requests of its verified or trust-boundary
  clients, or etcd's names-only peer requests that need no protocol knowledge
  (`addrsUnclaimed`'s parts (a) and (b), `Proof/runtime/Start.lean`, which program start turns
  into this token). The closed-world
  assumption of the gRPC boundary (`InvGrpc.lean`: the facts `grpcServes addr ...` say what the
  server at `addr` runs, forever): the program's addresses are its own. Nothing here produces
  it: a program's adequacy statement takes the free addresses of its initial world, one token
  each (item 9). `net.Listen(addr)` consumes it and never gives it back, so an address is
  listened on at most once in a run (Go would let a program listen again after closing the
  listener, or after grpc's `Serve` returned and closed it; such a program has no spec here).
* `netListenerAt l addr` (exclusive): the `net.Listener` `l` is bound at `addr` and accepts the
  connections dialed to `addr` by the program (no other process dials it, `netAddrFree`); nothing has
  accepted on it yet (grpc's `Serve` takes it,
  `grpc.start`).
-/
module

public import Perennial.Proof.ProofPrelude
public import GeneratedProof.net

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- **The address `addr` is the program's, unbound, dialed only by the program** (exclusive; see
the file header: `addrsUnclaimed`'s parts (a) and (b)). -/
axiom netAddrFree {GF : BundledGFunctors} [GooseExts] (addr : GoString) : IProp GF

/-- **The right to fix the HTTP protocol of the address `addr`** (exclusive; D39a, 2026-10-23,
rafthttp stage 6a): program start gives it once per address, with `netAddrFree addr`;
`http.reserve` (`Proof/net/http/Axioms.lean`) consumes it, fixing the address's protocol before
its listener exists (a raft member sends to its peers before they listen). Purely ghost: no Go
operation consumes or needs it. -/
axiom httpProtoFree {GF : BundledGFunctors} [GooseExts] (addr : GoString) : IProp GF

/-- **The listener `l` is bound at `addr`, unused** (exclusive; see the file header). -/
axiom netListenerAt {GF : BundledGFunctors} [GooseExts] (l : GoInterface) (addr : GoString) :
  IProp GF

/-! ### Numeric address literals (sweep repairs 1, W5) -/

/-- The pieces of `s` between the bytes `c` (`strings.Split`'s, at one byte). -/
def bytesSplit (c : w8) : List w8 → List (List w8)
  | [] => [[]]
  | b :: bs =>
    match bytesSplit c bs with
    | [] => [[b]]
    | p :: ps => if b = c then [] :: p :: ps else (b :: p) :: ps

/-- A decimal numeral without leading zeros (`"0"` itself allowed), its value. -/
def decNumeral? (s : List w8) : Option Nat :=
  if s = [] ∨ (2 ≤ s.length ∧ s.head? = some (W8 48)) then none else
  s.foldl (fun acc c => acc.bind fun n =>
    if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (10 * n + (c.toNat - 48)) else none) (some 0)

/-- **`a` is a canonical numeric IPv4 loopback address literal `127.d.d.d:p`** (decidable; sweep
repairs 1, W5, 2026-11-07): four octets `0..255`, the first `127`, and a port `1..65535`, each
decimal without leading zeros (until 2026-11-14 any first octet but the wildcard `0.0.0.0`).
(http-boundary-fix, 2026-11-14, etcd-grove-81's decision) Loopback only: Go's `http.Transport`
with `ProxyFromEnvironment` (rafthttp's round trippers) sends a request to a non-loopback host
through the proxy `HTTP_PROXY` names, whose own answers (`502`, `407`) no protocol admits; a
loopback host is never proxied (go1.27.3 `vendor/golang.org/x/net/http/httpproxy/proxy.go:178-185`,
`useProxy`; `examples/premisefix/httpproxy`). So it has no host name (`localhost` resolves through the
hosts file or DNS, `Listen` binds the first IPv4 address, and a dial tries them in RFC 6724 order:
`notes/axiom-review/alias-tokens.md`), no empty or wildcard host (a dual-stack bind overlapping
every address), no IPv6 and so no IPv4-mapped form, and no port `0` (`Listen` would pick a port).
Distinct such strings name distinct sockets, and Go dials a literal without resolution, so a dial
of `a` reaches only a listener bound at `a`. Program start gives `netAddrFree` and `httpProtoFree`
only for such literals (`goose_adequacy_start`'s `hAsLit`). -/
def netAddrLit (a : List w8) : Bool :=
  match bytesSplit (W8 58) a with
  | [host, port] =>
    match bytesSplit (W8 46) host with
    | [o₁, o₂, o₃, o₄] =>
      let os := [o₁, o₂, o₃, o₄].map decNumeral?
      os.all (fun o => o.any (· ≤ 255)) && decNumeral? o₁ == some 127 &&
        (decNumeral? port).any (fun p => 1 ≤ p && p ≤ 65535)
    | _ => false
  | _ => false

example : netAddrLit (go!"127.0.0.1:23790" : List w8) = true := by decide
example : netAddrLit (go!"localhost:24290" : List w8) = false := by decide
example : netAddrLit (go!"0.0.0.0:2379" : List w8) = false := by decide
example : netAddrLit (go!"127.0.0.1:024290" : List w8) = false := by decide
example : netAddrLit (go!"127.1.2.3:2380" : List w8) = true := by decide
example : netAddrLit (go!"10.0.0.1:2380" : List w8) = false := by decide

end EtcdGrove
end Perennial
