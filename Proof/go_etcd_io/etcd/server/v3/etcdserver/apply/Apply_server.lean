/-
The trust boundary: `apply.Apply` as the server's apply thread assumes it (`Spec/.../apply/
Apply_server.lean`); the function is proved against its own spec (`Apply.lean`), which the
server's proofs do not use yet (unit 3).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.Apply_server

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom apply.Apply_server.wp_proof : apply.Apply_server.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
