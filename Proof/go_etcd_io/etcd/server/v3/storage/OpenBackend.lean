/-
The trust boundary: `storage.OpenBackend(cfg, hooks)` (`server/storage/backend.go`: opens the backend at
`cfg.BackendPath()`, in a goroutine, logging when it takes long; names-only). Lean-first (no Rocq
counterpart); etcd PR #22518 (branch `pr-verify/etcd-22518`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.OpenBackend

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
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]
axiom storage.OpenBackend.wp_proof : storage.OpenBackend.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
