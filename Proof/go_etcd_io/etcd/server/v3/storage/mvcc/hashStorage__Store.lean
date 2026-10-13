/-
The trust boundary: `hashStorage.Store` (`hash.go` is names-only: its crc32 hasher has no
Perennial model; the hash never enters the model).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.hashStorage__Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

axiom mvcc.hashStorage.Store.wp_proof : mvcc.hashStorage.Store.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
