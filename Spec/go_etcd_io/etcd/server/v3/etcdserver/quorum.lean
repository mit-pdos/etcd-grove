/-
## `quorum(num)` (`util.go:46-48`)

**Users.** `isConnectedToQuorumSince`, `isConnectedToQuorumAfterAddingNewMemberSince` (2c's error
classification, `parseProposeCtxErr`; the member checks).

**Proof sketch.** Go's `int` arithmetic. **Changes**: from `specs-ref`'s `quorum.lean`.
**Margin.** Exact.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`quorum(n) = n / 2 + 1`** (Go's `int` arithmetic, wrapping). -/
def quorum.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.quorum)) (Val #n))
  {{ RET #(W64 (sint.Z n / 2 + 1)); True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
