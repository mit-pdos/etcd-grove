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

/-- `h.Sum64()` of a `New64a` hash: the FNV-1a hash of the bytes it has hashed. -/
abbrev fnv.sum64a.Sum64.spec : Prop :=
  ∀ (t : go.GoType) (v : val) (bs : List w8),
  {{ fnvHash (GF := GF) t v bs }}
    (App (Val #(methods t go!"Sum64" v)) (Val #()))
  {{ RET #(fnv64a bs); fnvHash t v bs }}

end spec

end bbolt
end EtcdGrove
end Perennial
