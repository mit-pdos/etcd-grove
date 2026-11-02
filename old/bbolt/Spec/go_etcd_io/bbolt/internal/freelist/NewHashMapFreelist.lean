module
public import Proof.go_etcd_io.bbolt.internal.freelist.HashImpl

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `NewHashMapFreelist()`: an empty `hashMap` freelist (its interface value). -/
abbrev NewHashMapFreelist.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist }}
    (App (Val #(functions NewHashMapFreelist [])) (Val #()))
  {{ (h s : Loc), RET #(hashMapImpl (GF := GF) h).iface; ownFL (hashMapImpl h) s FLState.empty }}

end spec

end bbolt
end EtcdGrove
end Perennial
