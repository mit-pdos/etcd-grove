/-
The trust boundary: `isConnectedToQuorumSince` (a query of the names-only transport, which only classifies an error).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.isConnectedToQuorumSince

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom isConnectedToQuorumSince.wp_proof : isConnectedToQuorumSince.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
