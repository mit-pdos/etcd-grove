module
public import Spec.go_etcd_io.bbolt.internal.freelist.NewArrayFreelist
public import Proof.go_etcd_io.bbolt.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `newFreelist(t)` of a type other than `"hashmap"`: an empty `array` freelist (the hashMap
freelist is not verified). -/
abbrev newFreelist.spec : Prop :=
  ∀ (t : GoString), t ≠ go!"hashmap" →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt }}
    (App (Val #(functions newFreelist [])) (Val #t))
  {{ (a s : Loc), RET #(arrayImpl (GF := GF) a).iface; ownFL (arrayImpl a) s FLState.empty }}

end spec

end bbolt
end EtcdGrove
end Perennial
