/-
`NewInBucket`'s proof (`internal/common/bucket.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.NewInBucket

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem NewInBucket.wp_proof : NewInBucket.spec (GF := GF) (hG := hG) := by
  intro root seq
  wp_start
  wp_auto
  iapply HΦ; itrivial

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
