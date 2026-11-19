/-
The trust boundary of `meta.ListAccessor` (see its spec). (k8s 7g, decided by etcd-grove-03
2026-11-19: option A.) Not proved from its body: its first row (the typed lists' `ListMeta`
accessors, promoted through `*PodList`, ...) is about `k8s.io/api/{core,apps}/v1` code, whose
`Assumptions` the driver's and the cache's Links do not reach, so a proof would restate the spec as
`Accessor`'s (any value in `List`'s type set: itself and `nil`) and move the typed lists' facts to a
pending hypothesis of the reflector's proofs (`notes/k8s-7g-trust.md` §11). Go evidence:
`examples/k8s/etcd3/trustspecs_test.go` `TestListAccessorObjList`.
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.meta.ListAccessor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimeta

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]

axiom ListAccessor.wp_proof : ListAccessor.spec (GF := GF) (hG := hG)

end proof

end apimeta
end EtcdGrove
end Perennial
