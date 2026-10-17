/-
The trust boundary: `(*zap.Logger).Named(s)` (`go.uber.org/zap`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Spec.go_uber_org.zap.Logger__Named

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

axiom zap.Logger.Named.wp_proof : zap.Logger.Named.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
