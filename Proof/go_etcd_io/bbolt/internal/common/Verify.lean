/-
`Verify`'s proof (`internal/common/verify.go`): a stub (`getEnvVerify`'s `os.Getenv` needs a
spec; `notes/bbolt-proof-plan.md`, batch 7).
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Verify

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

theorem Verify.wp_proof : Verify.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
