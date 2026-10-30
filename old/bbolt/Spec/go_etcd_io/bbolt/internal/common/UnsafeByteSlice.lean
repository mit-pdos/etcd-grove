module
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeAdd

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `UnsafeByteSlice(base, offset, i, j)` is `(*[MaxAllocSize]byte)(UnsafeAdd(base,
offset))[i:j:j]`: the bytes `i` to `j` of the memory `offset` bytes after `base`, as a
slice of length and capacity `j - i`. It panics unless `0 ≤ i ≤ j ≤ MaxAllocSize`. -/
abbrev UnsafeByteSlice.spec : Prop :=
  ∀ (base : Loc) (offset i j : w64),
  base.locCar ≠ 0 → 0 ≤ sint.Z i → sint.Z i ≤ sint.Z j → sint.Z j ≤ 2147483647 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (App (App (App (Val #(functions UnsafeByteSlice [])) (Val #base)) (Val #offset))
      (Val #i)) (Val #j))
  {{ RET #(slice.mk (base +ₗ (sint.Z offset + sint.Z i)) (j - i) (j - i)); True }}

end spec

end bbolt
end EtcdGrove
end Perennial
