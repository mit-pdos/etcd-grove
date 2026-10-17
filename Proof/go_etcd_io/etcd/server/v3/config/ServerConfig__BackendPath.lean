/-
The trust boundary: `(*config.ServerConfig).BackendPath()` (`server/config/config.go`:
`datadir.ToBackendFileName(c.DataDir)`, `<DataDir>/member/snap/db`; names-only). Lean-first (no
Rocq counterpart); etcd PR #22518 (branch `pr-verify/etcd-22518`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__BackendPath

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

axiom config.ServerConfig.BackendPath.wp_proof : config.ServerConfig.BackendPath.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
