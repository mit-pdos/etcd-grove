/-
The trust boundary: a context's `Value` at `internalRootContextKey{}` returns a fixed value
(etcd-io/etcd#22493, `pr-verify/etcd-22493`).
-/
module

public import Spec.context.ValueInternalRoot

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

axiom context.ValueInternalRoot.wp_proof : context.ValueInternalRoot.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
