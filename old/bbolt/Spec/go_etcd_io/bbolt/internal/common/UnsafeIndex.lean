module
public import Proof.go_etcd_io.bbolt.internal.common.Init

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

/-- `UnsafeIndex(base, offset, elemsz, n)` is `unsafe.Pointer(uintptr(base) + offset +
uintptr(n)*elemsz)`: the location of element `n` (of size `elemsz`) of an array `offset`
bytes after `base`, in 64-bit address arithmetic. -/
abbrev UnsafeIndex.spec : Prop :=
  ∀ (base : Loc) (offset elemsz n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (App (App (App (Val #(functions UnsafeIndex [])) (Val #base)) (Val #offset))
      (Val #elemsz)) (Val #n))
  {{ RET #(base +ₗ sint.Z (offset + n * elemsz)); True }}

end spec

end bbolt
end EtcdGrove
end Perennial
