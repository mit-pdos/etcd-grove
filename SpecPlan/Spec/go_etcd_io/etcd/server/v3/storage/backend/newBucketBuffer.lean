/-
`newBucketBuffer()` (`tx_buffer.go:160-162`): translated; internal (the buffers). A buffer of
`bucketBufferInitialSize` slots, none used. Changes: over `bbAt`. Margin: the capacity.
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

/-- **`newBucketBuffer()`**: an empty bucket buffer. -/
def newBucketBuffer.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend }} (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.newBucketBuffer)) (Val #()))
  {{ (bb : Loc), RET #bb; bbAt bb [] true }}

end spec

end Backend
end EtcdGrove
end Perennial
