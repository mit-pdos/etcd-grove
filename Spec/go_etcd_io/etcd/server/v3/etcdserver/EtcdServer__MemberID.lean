/-
## `(*EtcdServer).MemberID()` (`server.go:1758`)

**Users.** v3rpc's headers (`header.go:33`), interceptors (`interceptor.go:53`), `cluster3.PeerStep`, `restart.Run` (compared with `Leader()`).

**Proof sketch.** A read of a read-only field or an atomic load (`srvFields`' realization).

**Changes** (from `specs-ref`'s `EtcdServer__MemberID.lean` where it existed): over `srvMember`.

**Margin.** Exact.

Changes: verify-round (client-core's request): callers formatting the id (`s.MemberID().String()`, a pointer-receiver call on a copy) cite `types.ID.String_ptr`; URL lists `URLs__StringSlice_ptr`, `URLs__Len_ptr`.
Changes: re-review (RR2): over 2e's `srvFields` (the server literal's read-only fields), not `srvMember`: callable before the transport is set (`NewServer`'s own calls, `Process` from `tr.Start()` on, `start`); a caller holding `srvMember` uses `srvMember_fields`, one holding 2d's `srvNode` `srvNode_fields`.
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

/-- **`MemberID()`**: the member's id (`types.ID`). -/
def EtcdServer.MemberID.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvFields s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"MemberID")) (Val #()))
  {{ RET #(W64 id); True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
