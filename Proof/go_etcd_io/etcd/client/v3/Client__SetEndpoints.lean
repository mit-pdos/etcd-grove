/-
The trust boundary: `c.SetEndpoints(eps...)` (`client/v3/client.go`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__SetEndpoints

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

axiom Client.SetEndpoints.wp_proof : Client.SetEndpoints.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
