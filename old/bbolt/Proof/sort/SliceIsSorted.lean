module
public import Spec.sort.SliceIsSorted

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

/-- `sort.SliceIsSorted` checks adjacent elements with `less` (for `hashMap.Init`). An axiom:
the trust boundary (`sort` is translated names-only: `SliceIsSorted` reads the slice's length
by reflection; Perennial has no spec for it). -/
axiom sort.SliceIsSorted.wp_proof : sort.SliceIsSorted.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial
