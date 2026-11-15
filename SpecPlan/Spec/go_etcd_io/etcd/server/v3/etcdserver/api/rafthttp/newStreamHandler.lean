/-
## `newStreamHandler(t, pg, r, id, cid)`

**Users.** `Transport.Handler` (`pg` the transport itself, `id` its member's).

**Proof sketch.** The literal.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

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

/-- (internal) The stream handler of the transport. -/
def newStreamHandler.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid : w64) (r : GoInterface) (cid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ raftOk ν lid r }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newStreamHandler)) (Val #t)) (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty) #t))) (Val #r)) (Val #lid)) (Val #cid))
  {{ (h : GoInterface), RET #h; ∃ hp : Loc, ⌜h = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamHandler.ty) #hp⌝ ∗ sthAt hp ν lid }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
