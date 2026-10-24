/-
The trust boundary: `membership.StoreClusterVersionKey` (`membership` is names-only here).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.StoreClusterVersionKey

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom membership.StoreClusterVersionKey.wp_proof :
    membership.StoreClusterVersionKey.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
