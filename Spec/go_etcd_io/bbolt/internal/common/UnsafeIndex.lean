/-
`UnsafeIndex`'s spec (`internal/common/unsafe.go`; U0b of `notes/bbolt-proof-plan.md`).
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

/-- `UnsafeIndex(base, offset, elemsz, n)` is `unsafe.Add(base, offset + uintptr(n)*elemsz)`: the
address of element `n` (of size `elemsz`) of an array `offset` bytes past `base`, for a result in
`[0, maxAddr]`. -/
abbrev UnsafeIndex.spec : Prop :=
  ∀ (base : Loc) (offset elemsz n : w64),
  0 ≤ (base +ₗ sint.Z (offset + n * elemsz)).addr →
  (base +ₗ sint.Z (offset + n * elemsz)).addr ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (App (App (App (Val #(functions UnsafeIndex [])) (Val #base)) (Val #offset))
      (Val #elemsz)) (Val #n))
  {{ RET #(base +ₗ sint.Z (offset + n * elemsz)); True }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
