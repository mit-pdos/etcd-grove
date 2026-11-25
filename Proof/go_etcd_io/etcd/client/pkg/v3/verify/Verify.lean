/-
`verify.Verify`'s proof (`client/pkg/verify/verify.go`; etcdstorage, 2026-11-20, until then the
trust boundary, an axiom): over `IsVerificationEnabled`'s spec; both branches (`f` run and its
condition checked by `verifier`, or not), and with assertions off (`EtcdVerifyOff`) only the second.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Verify
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.IsVerificationEnabled

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.verify.Assumptions]

theorem verify.Verify.wp_proof
    (hEnabled : verify.IsVerificationEnabled.spec (GF := GF) (hG := hG)) :
    verify.Verify.spec (GF := GF) (hG := hG) := by
  intro msg f P
  wp_start as ⟨HP, Hf⟩
  wp_auto
  wp_apply hEnabled as %b %Hb
  icases Hf with (Hf | %Hvoff)
  · cases b
    · wp_auto
      iapply HΦ; iexact HP
    · wp_auto
      wp_bind (App (Val #f) (Val #()))
      iapply (wp_wand) $$ [Hf HP]
      · iapply Hf; iexact HP
      iintro %r ⟨%d, %hr, HP⟩
      subst hr
      try wp_auto
      wp_func_call
      wp_call
      try wp_auto
      iapply HΦ; iexact HP
  · obtain rfl : b = false := Hb Hvoff (Or.inl (by first | rfl | trivial))
    wp_auto
    iapply HΦ; iexact HP

end proof

end EtcdGrove
end Perennial
