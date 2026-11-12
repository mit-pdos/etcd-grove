/-
`bb.ForEach(visitor)` (`tx_buffer.go:189-196`): translated; internal. The visitor at each used
entry in order, stopping at its first error. Changes: over `visitOk`; integration Y: the visitor's own error returned (`visitOk vis P E`), the bytes kept by the visitor and lent against a share of the transaction's liveness (`lentAll … -∗ beLive`), as `rangeRes` (I6's finding: 4b's `Schema.txRd` row needs both). Margin: none.
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

/-- **`bb.ForEach(vis)`**: the visitor over the entries in order. -/
def bucketBuffer.ForEach.spec : Prop :=
  ∀ (bb : Loc) (l : List (GoString × GoString)) (w : Bool) (vis : GoFunc)
    (P : List Lent → IProp GF) (E : List Lent → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bbAt bb l w ∗ visitOk vis P E ∗ P [] }}
    (App (Val (bb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer.ty @!! go!"ForEach")) (Val #vis))
  {{ (err : GoInterface), RET #err; bbAt bb l w ∗ ∃ lt : List Lent,
      ⌜(lt.map Lent.ent) <+: l ∧ ∀ x ∈ lt, x.dq = DFrac.discard⌝ ∗
      ((⌜err = interface.nil ∧ lt.map Lent.ent = l⌝ ∗ P lt) ∨ (⌜err ≠ interface.nil⌝ ∗ E lt err)) }}

end spec

end Backend
end EtcdGrove
end Perennial
