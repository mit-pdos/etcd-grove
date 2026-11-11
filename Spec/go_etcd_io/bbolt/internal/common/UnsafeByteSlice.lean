/-
`UnsafeByteSlice`'s spec (`internal/common/unsafe.go`; U0b of `notes/bbolt-proof-plan.md`).
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

/-- `UnsafeByteSlice(base, offset, i, j)` is `unsafe.Slice((*byte)(unsafe.Add(base, offset)), j)[i:j:j]`:
the bytes `i` to `j` of the memory `offset` bytes past `base`, as a slice of length and capacity
`j - i`. It panics unless `0 ≤ i ≤ j`, and the memory must lie in the address space: premises. -/
abbrev UnsafeByteSlice.spec : Prop :=
  ∀ (base : Loc) (offset i j : w64),
  0 < (base +ₗ sint.Z offset).addr → (base +ₗ sint.Z offset).addr + sint.Z j ≤ maxAddr →
  0 ≤ sint.Z i → sint.Z i ≤ sint.Z j →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (App (App (App (Val #(functions UnsafeByteSlice [])) (Val #base)) (Val #offset))
      (Val #i)) (Val #j))
  {{ RET #(slice.mk ((base +ₗ sint.Z offset) +ₗ sint.Z i) (j - i) (j - i)); True }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
