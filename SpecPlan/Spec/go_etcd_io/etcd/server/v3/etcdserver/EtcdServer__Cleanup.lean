/-
## `(*EtcdServer).Cleanup()` (`server.go:943-963`)

**Users.** `run`'s deferred stop (2d: after the raft node's stop); `embed.StartEtcd` on an error
after `NewServer` and before `Start` (`embed/etcd.go:277`: `srvBuilt_closers`).

**Proof sketch.** `srvClosers s ds` holds the five fields (read-only) and their closers' resources:
`lessor.Stop` (3c), `kv.Close` (3e: its loops' readers back), `authStore.Close` (3d), the backend's
`Close` under `bemu` (4a: `beOpen`'s whole token, which the store's readers rebuilt), the compactor's
`Stop` (`V3compactor`). The backend's close gives the file at rest: `srvClosed ds`.

**Changes** (from `specs-ref`'s `EtcdServer__Cleanup.lean`, R2b-3c: `srvCleanupOwn` in auth-off
mode): one triple for every mode, over the closers' slot.

**Margin.** Called twice, Go panics (`lessor.Stop` closes a closed channel): the closers are taken
once.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

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

/-- **Closes the server's stores and backend**, giving the backend's file back at rest. -/
def EtcdServer.Cleanup.spec : Prop :=
  ∀ (s : Loc) (ds : Config.Dirs),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvClosers s ds }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Cleanup")) (Val #()))
  {{ RET #(); srvClosed ds }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
