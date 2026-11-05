/-
`Verify`'s proof (`internal/common/verify.go`): a stub, because `Verify.spec` is false (final wave
D): its precondition `WP f {{ _, Q }}` lets `f` panic (a WP's postcondition also receives
`PanicV p`), and `Verify(f)` then panics when `BBOLT_VERIFY` asks for the check, where the spec
promises `RET #()`. With `f`'s WP excluding a panic (`⌜v.isPanic = false⌝ ∗ Q`), it is proved:
`Lemmas/VerifyNP.Verify.wp_proofNP` (over `os.Getenv`'s and `strings.ToLower`'s trust-boundary
specs, `Spec/os/Getenv.lean`, `Spec/strings/ToLower.lean`); once the spec is corrected, this is it.
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
