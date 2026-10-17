/-
The trust boundary: `context.WithCancel(context.TODO())`: the trust boundary (pr-verify etcd#21714: `clientv3.newClient` of a `Config` with no `Context`). Perennial specifies `WithCancel` of an `isContext` parent, which `TODO()`'s is not. Lean-first (no Rocq counterpart).
-/
module

public import Spec.context.WithCancelTODO

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

axiom context.WithCancelTODO.wp_proof : context.WithCancelTODO.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
