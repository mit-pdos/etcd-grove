/-
## `(*closeNotifier).closeNotify()`

**Users.** `streamHandler.ServeHTTP`.

**Proof sketch.** A field read.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** The channel's facts are `cnAt`'s realization.
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

/-- (internal) The notifier's channel. -/
def closeNotifier.closeNotify.spec : Prop :=
  ∀ (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ cnAt n }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.closeNotifier.ty @!! go!"closeNotify")) (Val #()))
  {{ (ch : GoChan), RET #ch; True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
