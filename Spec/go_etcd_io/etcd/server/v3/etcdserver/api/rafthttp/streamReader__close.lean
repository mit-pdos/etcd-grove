/-
## `(*streamReader).close()`

**Users.** `decodeLoop`, `stop`.

**Proof sketch.** `closer.Close()` (`readerCloser`), `closer = nil`.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

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

/-- (internal) Under the lock: closes the registered stream, if any. -/
def streamReader.close.spec : Prop :=
  ∀ (cr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ srLocked cr }}
    (App (Val (cr @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader.ty @!! go!"close")) (Val #()))
  {{ RET #(); srLocked cr }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
