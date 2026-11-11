/-
`(*Meta).Copy`'s proof (`internal/common/meta.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Meta__Copy

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem Meta.Copy.wp_proof : Meta.Copy.spec (GF := GF) (hG := hG) := by
  intro l d v w dq
  wp_start as ⟨Hl, Hd⟩
  wp_auto
  iapply HΦ; iframe

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
