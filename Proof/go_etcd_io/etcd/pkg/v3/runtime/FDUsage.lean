/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/runtime/FDUsage.lean`, over the trusted model
(`TrustedCode/go_etcd_io/etcd/pkg/v3/runtime.lean`; prove-ps2-srvgoroutines, 2026-11-24).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.runtime.FDUsage
public import Proof.os.ErrorOk

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.runtime.Assumptions]

theorem runtime.FDUsage.wp_proof : runtime.FDUsage.spec (GF := GF) (hG := hG) := by
  wp_start
  (try wp_auto)
  wp_apply wp_ArbitraryInt as %e -
  by_cases he : e = W64 0
  · subst he
    rw [decide_eq_true (rfl : W64 0 = W64 0)]
    (try wp_auto)
    wp_apply wp_ArbitraryInt as %n -
    (try wp_auto)
    iapply HΦ
    isplitr
    · ipureintro; left; rfl
    iapply fmtErrorOkOrNil_nil
  · rw [decide_eq_false he]
    (try wp_auto)
    wp_apply wp_ArbitraryInt as %k -
    (try wp_auto)
    by_cases hk : k = W64 0
    · subst hk
      rw [decide_eq_true (rfl : W64 0 = W64 0)]
      (try wp_auto)
      wp_apply os.wp_pathError_ok _ _ e he as %pe #Hpe
      (try wp_auto)
      iapply HΦ
      isplitr
      · ipureintro; right; rfl
      iapply fmtErrorOkOrNil_of
      iexact Hpe
    · rw [decide_eq_false hk]
      (try wp_auto)
      wp_apply os.wp_pathError_ok _ _ e he as %pe #Hpe
      (try wp_auto)
      iapply HΦ
      isplitr
      · ipureintro; right; rfl
      iapply fmtErrorOkOrNil_of
      iexact Hpe

end proof

end EtcdGrove
end Perennial
