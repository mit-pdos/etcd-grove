/-
**etcd's test bridge, as part of the network** (`third_party/bridge`; `notes/client-cut-plan.md`
K1, `notes/decisions.md` D26; Lean-first, no Rocq counterpart). The bridge is a TCP proxy that
linkv3p puts between each client and its member, so that its partitioner can cut and mend the
link (`Blackhole`, `Unblackhole`, `DropConnections`). It is test infrastructure, not the system
under verification: a stand-in for the network, which the proof already lets fail (each attempt
of `ClientConn.Invoke` is a run of the handler served or an error, `InvGrpc.lean`). So its code is
not verified; the functions linkv3p calls have trust-boundary specs
(`Proof/github_com/mit_pdos/etcd_grove/third_party/bridge/<fn>.lean`, axioms) over one axiomatized
predicate:

* `bridgeAt b addr h` (exclusive): `b` is a bridge (`*bridge`, `New`'s) to the address `addr`,
  blackholed if `h`; its goroutines run on their own, without panicking.

`ownBridge br addr h` is the same of the interface value `New` returns (`Bridge`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Base
public import Proof.net.InvNet
public import Proof.google_golang_org.grpc.InvGrpc
public import Proof.google_golang_org.grpc.InvGrpcStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridge

open Iris Iris.BI github_com.mit_pdos.etcd_grove.third_party

/-- **`b` is a bridge to `addr`, blackholed if `h`** (exclusive; see the file header). -/
axiom bridgeAt {GF : BundledGFunctors} [GooseExts] (b : Loc) (addr : GoString) (h : Bool) :
  IProp GF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The interface value `br` is a bridge to `addr`, blackholed if `h`** (exclusive). -/
def ownBridge (br : GoInterface) (addr : GoString) (h : Bool) : IProp GF :=
  iprop(∃ b : Loc,
    ⌜br = interface.mkOk (go.GoType.PointerType bridge.bridge.ty) #b⌝ ∗ bridgeAt b addr h)

end defs

end bridge
end EtcdGrove
end Perennial
