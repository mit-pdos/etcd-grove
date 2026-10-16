/-
The trust boundary: `(*mvcc.store).HashStorage()` (`kvstore.go`: `return s.hashes`): names-only. Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16), for `NewServer`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__HashStorage

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

axiom mvcc.store.HashStorage.wp_proof : mvcc.store.HashStorage.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
