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

/-- `LoadPageMeta(buf)`: the `Meta` after the page header in `buf` (`&buf[16]`); it panics
unless `buf` is longer than the header. -/
abbrev LoadPageMeta.spec : Prop :=
  ∀ (buf : GoSlice),
  16 < sint.Z buf.len → buf.ptr.locCar ≠ 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (Val #(functions LoadPageMeta [])) (Val #buf))
  {{ RET #(buf.ptr +ₗ 16); True }}

end spec

end bbolt
end EtcdGrove
end Perennial
