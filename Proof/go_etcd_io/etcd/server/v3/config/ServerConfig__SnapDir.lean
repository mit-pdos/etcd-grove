/-
The trust boundary: `(*config.ServerConfig).SnapDir()` (`server/config/config.go`: `filepath.Join(c.MemberDir(),
"snap")`; names-only). Lean-first (no Rocq counterpart); etcd PR #22518 (branch
`pr-verify/etcd-22518`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__SnapDir

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

axiom config.ServerConfig.SnapDir.wp_proof : config.ServerConfig.SnapDir.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
