/-
The trust boundary: `NewHashStorage` (`hash.go`, names-only: the compaction's hashes).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewHashStorage

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

axiom mvcc.NewHashStorage.wp_proof : mvcc.NewHashStorage.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
