/-
**The network's addresses, for a server's listener** (item 4, the server start; Lean-first, no
Rocq counterpart). Perennial has no network model; these two axiomatized predicates are the
vocabulary of `net.Listen`'s trust-boundary spec (`Spec/net/Listen.lean`) and of grpc's server
start (`Proof/google_golang_org/grpc/InvGrpcServer.lean`).

* `netAddrFree addr` (exclusive): no listener of this program or of any other process is, or
  will be (other than through this token), bound at the address `addr`. The closed-world
  assumption of the gRPC boundary (`InvGrpc.lean`: the facts `grpcServes addr ...` say what the
  server at `addr` runs, forever): the program's addresses are its own. Nothing here produces
  it: a program's adequacy statement takes the free addresses of its initial world, one token
  each (item 9). `net.Listen(addr)` consumes it and never gives it back, so an address is
  listened on at most once in a run (Go would let a program listen again after closing the
  listener, or after grpc's `Serve` returned and closed it; such a program has no spec here).
* `netListenerAt l addr` (exclusive): the `net.Listener` `l` is bound at `addr` and accepts the
  connections dialed to `addr`; nothing has accepted on it yet (grpc's `Serve` takes it,
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

/-- **The address `addr` is the program's, unbound** (exclusive; see the file header). -/
axiom netAddrFree {GF : BundledGFunctors} [FfiSyntax] (addr : GoString) : IProp GF

/-- **The right to fix the HTTP protocol of the address `addr`** (exclusive; D34a, 2026-10-23,
rafthttp stage 6a): program start gives it once per address, with `netAddrFree addr`;
`http.reserve` (`Proof/net/http/Axioms.lean`) consumes it, fixing the address's protocol before
its listener exists (a raft member sends to its peers before they listen). Purely ghost: no Go
operation consumes or needs it. -/
axiom httpProtoFree {GF : BundledGFunctors} [FfiSyntax] (addr : GoString) : IProp GF

/-- **The listener `l` is bound at `addr`, unused** (exclusive; see the file header). -/
axiom netListenerAt {GF : BundledGFunctors} [FfiSyntax] (l : GoInterface) (addr : GoString) :
  IProp GF

end EtcdGrove
end Perennial
