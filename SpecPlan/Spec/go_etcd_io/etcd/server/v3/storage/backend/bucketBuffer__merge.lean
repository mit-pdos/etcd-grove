/-
`bb.merge(src)` (`tx_buffer.go:209-220`): translated; internal. `src`'s entries appended
(`add`), then, if the old part was not empty, `dedupe` unless the old part's last key is below the
new part's first (`src.buf[0]`: `src` must have a slot, a writable buffer). Both parts sorted, each
key once. Changes: over `mergeOk`; round 1 (S5): the premises and the code's test. Margin: none.
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

/-- **`bb.merge(src)`**: `mergeOk`. -/
def bucketBuffer.merge.spec : Prop :=
  ∀ (bb src : Loc) (l m : List (GoString × GoString)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bbAt bb l true ∗ bbAt src m true ∗
      ⌜l.Pairwise (fun a b => go.GoStringLt a.1 b.1) ∧ m.Pairwise (fun a b => go.GoStringLt a.1 b.1)⌝ }}
    (App (Val (bb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer.ty @!! go!"merge")) (Val #src))
  {{ RET #(); bbAt src m true ∗ ∃ r, ⌜mergeOk l m r⌝ ∗ bbAt bb r true }}

end spec

end Backend
end EtcdGrove
end Perennial
