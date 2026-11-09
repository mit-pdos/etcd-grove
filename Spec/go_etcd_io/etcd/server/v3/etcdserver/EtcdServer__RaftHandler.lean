/-
## `(*EtcdServer).RaftHandler()` (`server.go:646`)

**Users.** `etcdstart.NewMember`, `restart.startMember` (`go http.Serve(l, s.RaftHandler())` on the
member's peer listener, before `Start`); `embed`'s peer handler. Snippet: `etcdserverboot/boot.go`.

**Proof sketch.** `s.r.transport` (read-only since `NewServer`, `srvMember`), 2f's
`Transport.Handler.spec`: `raftHandler h γ id`.

**Changes** (from `specs-ref`'s `EtcdServer__RaftHandler.lean`, over `srvNetMember γn srv id τ`):
over `srvMember`.

**Margin.** None.
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

/-- **`RaftHandler()`**: the member's raft HTTP handler. -/
def EtcdServer.RaftHandler.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"RaftHandler")) (Val #()))
  {{ (h : GoInterface), RET #h; raftHandler h γ id }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
