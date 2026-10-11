/-
The trust boundary: `store.restore` (`kvstore.go`, untranslated), on a fresh backend.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__restore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

axiom mvcc.store.restore.wp_proof : mvcc.store.restore.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
