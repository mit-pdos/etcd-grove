/-
## `NewInBucket(root, seq)` (`internal/common/bucket.go`)

**Users.** db.go:700 (`init`).
**Proof sketch.** a struct literal.
**Changes.** from `specs-ref`'s file of the same name (unchanged).
**Margin.** none: the post is what the code computes.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BboltCommon

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `NewInBucket(root, seq)`: the header value. -/
def NewInBucket.spec : Prop :=
  ∀ (root : Pgid) (seq : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (App (Val (@! go_etcd_io.bbolt.internal.common.NewInBucket)) (Val #root)) (Val #seq))
  {{ RET #({ root' := root, sequence' := seq } : InBucket); True }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
