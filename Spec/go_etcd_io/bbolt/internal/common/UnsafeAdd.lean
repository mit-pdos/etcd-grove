/-
`UnsafeAdd`'s spec (`internal/common/unsafe.go`; U0b of `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace common

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `UnsafeAdd(base, offset)` is `unsafe.Add(base, offset)`: `base` moved by `offset` bytes (read as
a signed word), for a result in `[0, maxAddr]` (outside it the model's pointer addition is
stuck). -/
abbrev UnsafeAdd.spec : Prop :=
  ∀ (base : Loc) (offset : w64),
  0 ≤ (base +ₗ sint.Z offset).addr → (base +ₗ sint.Z offset).addr ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (App (Val #(functions UnsafeAdd [])) (Val #base)) (Val #offset))
  {{ RET #(base +ₗ sint.Z offset); True }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
