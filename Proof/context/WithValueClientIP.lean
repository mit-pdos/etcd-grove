/-
The trust boundary: `context.WithValue` at the key `auth.ClientIPContextKey{}` (PR etcd#22259;
Perennial translates `context` without `WithValue`'s body).
-/
module

public import Spec.context.WithValueClientIP

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
variable [package_sem : context.Assumptions]

axiom context.WithValueClientIP.wp_proof : context.WithValueClientIP.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
