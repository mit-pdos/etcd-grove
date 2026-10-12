/-
The trust boundary: `config.ServerConfig.ReqTimeout` (arithmetic on two configuration fields (no overflow at sane values); total).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ReqTimeout

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom config.ServerConfig.ReqTimeout.wp_proof : config.ServerConfig.ReqTimeout.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
