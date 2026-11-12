/-
`NewInBucket`'s spec (`internal/common/bucket.go`; U0b of `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace common

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `NewInBucket(root, seq)`: the bucket header with that root page and sequence. -/
abbrev NewInBucket.spec : Prop :=
  ∀ (root seq : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (App (Val #(functions NewInBucket [])) (Val #root)) (Val #seq))
  {{ RET #(InBucket.mk root seq); True }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
