/-
## `(*EtcdServer).KV()` (`server.go:2415`): translated

**Users.** 2a's maintenance (`KV().Rev()`, hashes), the watch server (through `Watchable`), with
`isServer`; `NewUberApplier` (`server.go:1184`, inside `NewServer`, before `isServer`) and the
apply thread's `snapshot` (`KV().Commit()`). **Proof sketch.** A read of the read-only field.
**Changes**: from `specs-ref`. Re-review (RR2): the premise is the field's persistent points-to
(the caller's source: `isServer_kv` with `srvWatchable` of the value, `srvNode_kv`,
`srvStores_kv`), not `isServer`, which `NewServer` and the apply thread do not hold; the post
returns that value. **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

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

/-- **The server's watchable store**: the value of the read-only field `s.kv`. -/
def EtcdServer.KV.spec : Prop :=
  ∀ (s : Loc) (w : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"kv" s ↦□ w }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"KV")) (Val #()))
  {{ RET #w; True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
