/-
`bb.merge(src)` (`tx_buffer.go:209-220`): translated; internal. `src`'s entries appended
(`add`), then `dedupe` unless they all follow the old ones. Changes: over `mergeOk`. Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal

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

/-- **`bb.merge(src)`**: `mergeOk`. -/
def bucketBuffer.merge.spec : Prop :=
  ∀ (bb src : Loc) (l m : List (GoString × GoString)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bbAt bb l ∗ bbAt src m }}
    (App (Val (bb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer.ty @!! go!"merge")) (Val #src))
  {{ RET #(); bbAt src m ∗ ∃ r, ⌜mergeOk l m r⌝ ∗ bbAt bb r }}

end spec

end Backend
end EtcdGrove
end Perennial
