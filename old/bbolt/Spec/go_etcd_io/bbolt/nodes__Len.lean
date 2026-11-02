module
public import Proof.go_etcd_io.bbolt.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `s.Len()`: the number of nodes. -/
abbrev nodes.Len.spec : Prop :=
  ∀ (s : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt }}
    (App (Val (s @!! nodes.ty @!! go!"Len")) (Val #()))
  {{ RET #s.len; True }}

end spec

end bbolt
end EtcdGrove
end Perennial
