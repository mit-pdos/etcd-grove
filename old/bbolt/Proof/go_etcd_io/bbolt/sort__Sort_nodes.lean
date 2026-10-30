module
public import Spec.go_etcd_io.bbolt.sort__Sort_nodes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `sort.Sort` on a slice of `nodes` permutes it, reading what `nodes.Less` reads. An axiom:
the trust boundary (`sort.Sort` is not translated; Perennial has no spec for it). -/
axiom sort.Sort.wp_nodes : sort.Sort.nodes_spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial
