/-
The trust boundary: `membership.MustParseMemberIDFromKey` (`membership` is names-only here).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.MustParseMemberIDFromKey

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

axiom membership.MustParseMemberIDFromKey.wp_proof :
    membership.MustParseMemberIDFromKey.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
