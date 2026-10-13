/-
The trust boundary: `version.Cluster(v)` (`api/v3/version`): names-only (the server's `start` logs it).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.version.Cluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom version.Cluster.wp_proof : version.Cluster.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
