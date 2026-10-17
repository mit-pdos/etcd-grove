/-
The trust boundary: `v3compactor.newRevision` (names only).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newRevision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom v3compactor.newRevision.wp_proof : v3compactor.newRevision.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
