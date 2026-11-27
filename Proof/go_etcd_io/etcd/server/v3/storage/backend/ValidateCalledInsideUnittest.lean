/-
`backend.ValidateCalledInsideUnittest`'s proof (`verify.go`; etcdstorage, 2026-11-20, until then the trust boundary, an
axiom): with `ETCD_VERIFY` off (`EtcdVerifyOff`), `verifyLockEnabled` (`verify.IsVerificationEnabled`
of `lock`) is false and it returns before reading the stack.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.ValidateCalledInsideUnittest
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.IsVerificationEnabled

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [verify_sem : go_etcd_io.etcd.client.pkg.v3.verify.Assumptions]

theorem backend.ValidateCalledInsideUnittest.wp_proof
    (hEnabled : verify.IsVerificationEnabled.spec (GF := GF) (hG := hG)) :
    backend.ValidateCalledInsideUnittest.spec (GF := GF) (hG := hG) := by
  intro lg
  wp_start as %Hvoff
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  wp_apply hEnabled as %b %Hb
  obtain rfl : b = false := Hb Hvoff (Or.inr (by first | rfl | trivial))
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
