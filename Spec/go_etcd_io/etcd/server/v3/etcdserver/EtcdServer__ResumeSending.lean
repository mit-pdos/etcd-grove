/-
`(*EtcdServer).ResumeSending()` (`server.go:2213`): `s.r.resumeSending()`, which asserts the transport is `rafthttp.Pausable` and calls `Resume()`.

**Users**: the integration framework's `Member.Resume` (`tests/framework/integration/cluster.go:1170`). Snippet `etcdserverboot/boot.go` `ReqPartition`.

**Proof sketch**: `srvMember`'s realization holds `s.r.transport`, the member's `*rafthttp.Transport` (2f's `isTransport`), so the type assertion succeeds; `Transport.Resume.spec` (the caller's `threadTok`).

**Changes**: verify round (A8-completeness F5; rafthttp's request): new. `raftNode.resumeSending` is not translated (inlined here).

**Margin**: none.
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

/-- **`ResumeSending()`**: the transport sends again. -/
def EtcdServer.ResumeSending.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"ResumeSending")) (Val #()))
  {{ RET #(); threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
