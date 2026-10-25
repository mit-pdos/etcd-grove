/-
The trust boundary: `zapcore.CheckedEntry.Write` (`go.uber.org/zap/zapcore` is names-only).
-/
module

public import Spec.go_uber_org.zap.zapcore.CheckedEntry__Write

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom zapcore.CheckedEntry.Write.wp_proof : zapcore.CheckedEntry.Write.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
