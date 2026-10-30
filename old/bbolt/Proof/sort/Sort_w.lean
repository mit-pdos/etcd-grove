module
public import Spec.sort.Sort_w

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `sort.Sort` sorts the writer's dirty pages by id. An axiom: the trust boundary (`sort.Sort`
is not translated; Perennial has no spec for it). -/
axiom sort.Sort.wp_wproof : sort.Sort.wspec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial
