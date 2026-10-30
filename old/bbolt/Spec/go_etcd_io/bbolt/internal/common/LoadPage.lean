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

/-- `LoadPage(buf)`: `buf`'s first byte read as a `*Page` (`&buf[0]`); it panics if `buf` is
empty. -/
abbrev LoadPage.spec : Prop :=
  ∀ (buf : GoSlice),
  0 < sint.Z buf.len →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (Val #(functions LoadPage [])) (Val #buf))
  {{ RET #buf.ptr; True }}

end spec

end bbolt
end EtcdGrove
end Perennial
