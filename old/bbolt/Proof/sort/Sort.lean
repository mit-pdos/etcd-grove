module
public import Spec.sort.Sort

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `sort.Sort` sorts (for bbolt's slices of `uint64`s). An axiom: the trust boundary
(`sort.Sort` is not translated; Perennial has no spec for it). -/
axiom sort.Sort.wp_proof : sort.Sort.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial
