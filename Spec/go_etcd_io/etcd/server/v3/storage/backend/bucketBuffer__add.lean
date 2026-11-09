/-
`bb.add(k, v)` (`tx_buffer.go:198-206`): translated; internal. Appends, growing the slice by half
when full. Changes: over `bbAt`. Margin: none.
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

/-- **`bb.add(k, v)`**: the entry appended. -/
def bucketBuffer.add.spec : Prop :=
  ∀ (bb : Loc) (l : List (GoString × GoString)) (ks vs : GoSlice) (k v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ bbAt bb l ∗ ks ↦*□ k ∗ vs ↦*□ v }}
    (App (App (Val (bb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer.ty @!! go!"add")) (Val #ks)) (Val #vs))
  {{ RET #(); bbAt bb (l ++ [(k, v)]) }}

end spec

end Backend
end EtcdGrove
end Perennial
