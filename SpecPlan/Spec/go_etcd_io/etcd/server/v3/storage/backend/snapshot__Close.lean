/-
## `(*snapshot).Close()` (`backend.go:1101-1105`): translated

**Users.** 2d's `newSnapshotReaderCloser` (`snapshot_merge.go:70`), the maintenance server
(`maintenance.go`). Snippet `snapshot.go`.

**Proof sketch.** `close(s.stopc)` (the monitor's channel, closed once: `beSnap` is consumed),
`<-s.donec` (the monitor exits), bbolt's `Rollback` of the read transaction (4c: `nil` for an open
read transaction; the reader slot back).

**Changes.** From `specs-ref`'s: the reader slot back. verify-round: over `beSnapN` (A11 F5). **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`s.Close()`**: the snapshot's read transaction ends; `nil`, and the reader slot back. -/
def snapshot.Close.spec : Prop :=
  ∀ (γ : BeNames) (s : Loc) (I : Image) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beSnapN γ s I n }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗ beRdToks γ 1 }}

end spec

end Backend
end EtcdGrove
end Perennial
