/-
## `NewLockServer(c)` (`lock.go`): translated

**Users.** embed (`embed/serve.go:149-150`: `v3lockpb.RegisterLockServer(gs, v3lock.NewLockServer(v3c))`) and the integration framework (`cluster.go:987-988`), over the in-process client `v3client.New(s)`. **Proof sketch.** A struct literal. **Changes**: new.
**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3lock

open Iris Iris.BI EtcdModel ClientV3 Concurrency

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Assumptions]

/-- **The Lock service over the client `c`.** -/
def NewLockServer.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.NewLockServer)) (Val #c))
  {{ (ls : GoInterface), RET #ls; ∃ p : Loc,
      ⌜ls = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.lockServer.ty) #p⌝ ∗ isLockServer p c }}

end spec

end V3lock
end EtcdGrove
end Perennial
