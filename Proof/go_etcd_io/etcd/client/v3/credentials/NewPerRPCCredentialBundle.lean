/-
The trust boundary: `credentials.NewPerRPCCredentialBundle()` (`client/v3/credentials`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.NewPerRPCCredentialBundle

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

axiom credentials.NewPerRPCCredentialBundle.wp_proof : credentials.NewPerRPCCredentialBundle.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
