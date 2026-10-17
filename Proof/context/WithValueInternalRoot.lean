/-
The trust boundary: `context.WithValue` at the auth store's `internalRootContextKey{}`
(etcd-io/etcd#22493, `pr-verify/etcd-22493`).
-/
module

public import Spec.context.WithValueInternalRoot

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

axiom context.WithValueInternalRoot.wp_proof :
  context.WithValueInternalRoot.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
