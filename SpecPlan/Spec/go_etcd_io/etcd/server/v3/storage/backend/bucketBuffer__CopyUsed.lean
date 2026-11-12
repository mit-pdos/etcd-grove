/-
`bb.CopyUsed()` (`tx_buffer.go:244-253`): translated; internal. `verify.Assert` (off: `envOk`), a
fresh buffer of the used entries, with no spare slot (not writable). Changes: `envOk`; round 1
(S5): the copy not writable. Margin: none.
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

/-- **`bb.CopyUsed()`**: a fresh buffer with the same entries. -/
def bucketBuffer.CopyUsed.spec : Prop :=
  ∀ (bb : Loc) (l : List (GoString × GoString)) (w : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ envOk ∗ bbAt bb l w }}
    (App (Val (bb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer.ty @!! go!"CopyUsed")) (Val #()))
  {{ (c : Loc), RET #c; bbAt bb l w ∗ bbAt c l false }}

end spec

end Backend
end EtcdGrove
end Perennial
