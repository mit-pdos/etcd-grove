/-
## `(*peer).update(urls)`

**Users.** `Transport.UpdatePeer`.

**Proof sketch.** `urlPicker.update`.

**Changes.** New (no old spec).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) Replaces the peer's URLs (each host a peer address). -/
def peer.update.spec : Prop :=
  ∀ (p : Loc) (ν : Net) (lid pid : w64) (urls : GoSlice) (hs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ peerAt p ν lid pid ∗ urlsAt urls hs ∗ ⌜hs ≠ []⌝ ∗ ([∗list] a ∈ hs, peerAddr ν a) }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer.ty @!! go!"update")) (Val #urls))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
