/-
## `(*Message).CloseWithError(err)` (`message.go:57-66`): trusted (names only)

**Users.** rafthttp's snapshot sender (2f), once per message. **Why it is true.** The reader's
`Close` (once: `msgClose`), then one send on the buffered channel (never blocks). **Changes** (from
`specs-ref`'s `Message__CloseWithError.lean`): the once-only close (the sweep's B3-3).
**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Api
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Snap

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

/-- **Closes the message's reader** and notifies. -/
def Message.CloseWithError.spec : Prop :=
  ∀ (p : Loc) (to tot : w64) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗ isMessage p to tot ∗ msgClose p }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message.ty @!! go!"CloseWithError")) (Val #err))
  {{ RET #(); True }}

end spec

end Snap
end EtcdGrove
end Perennial
