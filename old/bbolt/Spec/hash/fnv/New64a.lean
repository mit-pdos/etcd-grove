module
public import Proof.hash.fnv.Model
public import Proof.go_etcd_io.bbolt.internal.common.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `fnv.New64a()`: a `hash.Hash64` (some dynamic type and value) that has hashed nothing. -/
abbrev fnv.New64a.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val #(functions _root_.Perennial.hash.fnv.New64a [])) (Val #()))
  {{ (t : go.GoType) (v : val), RET #(interface.mkOk t v); fnvHash (GF := GF) t v [] }}

end spec

end bbolt
end EtcdGrove
end Perennial
