/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewAuth.lean`: a trust-boundary axiom (item 5, client construction). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewAuth

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

/-- **Trust boundary** (item 5): `NewAuth(c)` returns `&authClient{remote: RetryAuthClient(c), callOpts: c.callOpts}`: allocations and reads of `c`'s
fields, which `New` set and never writes again; it returns. -/
axiom NewAuth.wp_proof : NewAuth.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
