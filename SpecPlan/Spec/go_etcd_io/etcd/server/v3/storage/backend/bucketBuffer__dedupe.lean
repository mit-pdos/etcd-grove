/-
`bb.dedupe()` (`tx_buffer.go:223-236`): translated; internal. `sort.Stable` by key, then the last
of each run kept. Changes: over `dedupeOk`. Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal

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

/-- **`bb.dedupe()`**: `dedupeOk`. -/
def bucketBuffer.dedupe.spec : Prop :=
  ∀ (bb : Loc) (l : List (GoString × GoString)) (w : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bbAt bb l w }}
    (App (Val (bb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer.ty @!! go!"dedupe")) (Val #()))
  {{ RET #(); ∃ r, ⌜dedupeOk l r⌝ ∗ bbAt bb r w }}

end spec

end Backend
end EtcdGrove
end Perennial
