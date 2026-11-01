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

/-- `UnsafeAdd(base, offset)` is `unsafe.Pointer(uintptr(base) + offset)`: the location
`offset` bytes (cells) after `base`, the offset read as a signed word as `unsafe.Add` does
(an address is 64 bits, so the two agree on the address). -/
abbrev UnsafeAdd.spec : Prop :=
  ∀ (base : Loc) (offset : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (App (Val #(functions UnsafeAdd [])) (Val #base)) (Val #offset))
  {{ RET #(base +ₗ sint.Z offset); True }}

end spec

end bbolt
end EtcdGrove
end Perennial
