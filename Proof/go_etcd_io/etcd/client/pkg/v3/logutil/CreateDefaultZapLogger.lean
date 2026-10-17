/-
The trust boundary: `logutil.CreateDefaultZapLogger(level)` (`client/pkg/v3/logutil`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.logutil.CreateDefaultZapLogger

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

axiom logutil.CreateDefaultZapLogger.wp_proof : logutil.CreateDefaultZapLogger.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
