/-
## `NewElectionServer(c)` (`election.go`): translated

**Users.** v3rpc's server registration (`v3rpc.Server`, 2a, with `v3client.New(s)`).
**Proof sketch.** A struct literal. **Changes**: new. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3election

open Iris Iris.BI EtcdModel ClientV3 Concurrency

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Assumptions]

/-- **The Election service over the client `c`.** -/
def NewElectionServer.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3election.NewElectionServer)) (Val #c))
  {{ (es : GoInterface), RET #es; ∃ p : Loc,
      ⌜es = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer.ty) #p⌝ ∗ isElectionServer p c }}

end spec

end V3election
end EtcdGrove
end Perennial
