/-
The trust boundary: `credentials.NewTransportCredential(cfg)` (`client/v3/credentials`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.NewTransportCredential

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

axiom credentials.NewTransportCredential.wp_proof : credentials.NewTransportCredential.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
