/-
The trust boundary: `unsafeHashByRev` (`hash.go` is names-only but for `kvHashIncludes`: the
hasher's crc32 has no Perennial model, and the backend's `UnsafeForEach` no spec; pr-verify/etcd-21202).
Its revision fields are what `newKVHasher` stores and `kvHasher.Hash` returns (read in the Go code).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.unsafeHashByRev

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

axiom mvcc.unsafeHashByRev.wp_proof : mvcc.unsafeHashByRev.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
