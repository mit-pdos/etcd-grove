/-
`bb.ForEach(visitor)` (`tx_buffer.go:189-196`): translated; internal. The visitor at each used
entry in order, stopping at its first error. Changes: over `visitOk`. Margin: none.
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

/-- **`bb.ForEach(vis)`**: the visitor over the entries in order. -/
def bucketBuffer.ForEach.spec : Prop :=
  ∀ (bb : Loc) (l : List (GoString × GoString)) (vis : GoFunc)
    (P : List (GoString × GoString) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bbAt bb l ∗ visitOk vis P ∗ P [] }}
    (App (Val (bb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer.ty @!! go!"ForEach")) (Val #vis))
  {{ (err : GoInterface), RET #err; bbAt bb l ∗
      ((⌜err = interface.nil⌝ ∗ P l) ∨ (⌜err ≠ interface.nil⌝ ∗ ∃ j, P (l.take j))) }}

end spec

end Backend
end EtcdGrove
end Perennial
