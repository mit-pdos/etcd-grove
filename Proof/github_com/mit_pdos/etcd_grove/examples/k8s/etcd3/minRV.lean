module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.minRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvBytes

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem minRV.wp_proof
    (wp_rvBytes : rvBytes.spec (GF := GF) (hG := hG)) :
    minRV.spec (GF := GF) (hG := hG) := by
  intro m d c hasC
  wp_start as -
  wp_auto
  by_cases h1 : m < W64 30
  · rw [decide_eq_true (show uint.Z m < uint.Z (W64 30) by word)]
    wp_auto
    rw [show ([] : GoString) = minRVL m d c hasC by unfold minRVL; rw [if_pos (show m < 30 from h1)]]
    iapply HΦ; itrivial
  rw [decide_eq_false (show ¬ uint.Z m < uint.Z (W64 30) by word)]
  wp_auto
  by_cases h2 : m < W64 45
  · rw [decide_eq_true (show uint.Z m < uint.Z (W64 45) by word)]
    wp_auto
    wp_apply wp_rvBytes
    (try wp_auto)
    rw [show rvBytes (W64 0) = minRVL m d c hasC by
      unfold minRVL; rw [if_neg (show ¬ m < 30 from h1), if_pos (show m < 45 from h2)]; rfl]
    iapply HΦ; itrivial
  rw [decide_eq_false (show ¬ uint.Z m < uint.Z (W64 45) by word)]
  wp_auto
  by_cases h3 : m < W64 55
  · rw [decide_eq_true (show uint.Z m < uint.Z (W64 55) by word)]
    wp_auto
    wp_apply wp_rvBytes
    (try wp_auto)
    rw [show rvBytes (W64 1) = minRVL m d c hasC by
      unfold minRVL; rw [if_neg (show ¬ m < 30 from h1), if_neg (show ¬ m < 45 from h2), if_pos (show m < 55 from h3)]; rfl]
    iapply HΦ; itrivial
  rw [decide_eq_false (show ¬ uint.Z m < uint.Z (W64 55) by word)]
  wp_auto
  cases hasC
  · wp_auto
    rw [show ([] : GoString) = minRVL m d c false by
      unfold minRVL; rw [if_neg (show ¬ m < 30 from h1), if_neg (show ¬ m < 45 from h2), if_neg (show ¬ m < 55 from h3), if_pos (show (!false) = true from rfl)]]
    iapply HΦ; itrivial
  wp_auto
  by_cases h4 : m < W64 84
  · rw [decide_eq_true (show uint.Z m < uint.Z (W64 84) by word)]
    wp_auto
    wp_apply wp_rvBytes
    (try wp_auto)
    rw [show rvBytes c.ResourceVersion' = minRVL m d c true by
      unfold minRVL; rw [if_neg (show ¬ m < 30 from h1), if_neg (show ¬ m < 45 from h2), if_neg (show ¬ m < 55 from h3), if_neg (by decide), if_pos (show m < 84 from h4)]]
    iapply HΦ; itrivial
  rw [decide_eq_false (show ¬ uint.Z m < uint.Z (W64 84) by word)]
  wp_auto
  by_cases h5 : m < W64 98
  · rw [decide_eq_true (show uint.Z m < uint.Z (W64 98) by word)]
    wp_auto
    by_cases h6 : c.ResourceVersion' ≤ d
    · rw [decide_eq_true (show uint.Z c.ResourceVersion' ≤ uint.Z d by word)]
      wp_auto
      wp_apply wp_rvBytes
      (try wp_auto)
      rw [show rvBytes (W64 1) = minRVL m d c true by
        unfold minRVL
        rw [if_neg (show ¬ m < 30 from h1), if_neg (show ¬ m < 45 from h2), if_neg (show ¬ m < 55 from h3), if_neg (by decide), if_neg (show ¬ m < 84 from h4), if_pos (show m < 98 from h5), if_pos h6]; rfl]
      iapply HΦ; itrivial
    · rw [decide_eq_false (show ¬ uint.Z c.ResourceVersion' ≤ uint.Z d by word)]
      wp_auto
      wp_apply wp_rvBytes
      (try wp_auto)
      rw [show rvBytes (c.ResourceVersion' - d) = minRVL m d c true by
        unfold minRVL
        rw [if_neg (show ¬ m < 30 from h1), if_neg (show ¬ m < 45 from h2), if_neg (show ¬ m < 55 from h3), if_neg (by decide), if_neg (show ¬ m < 84 from h4), if_pos (show m < 98 from h5), if_neg h6]]
      iapply HΦ; itrivial
  rw [decide_eq_false (show ¬ uint.Z m < uint.Z (W64 98) by word)]
  wp_auto
  wp_apply wp_rvBytes
  (try wp_auto)
  rw [show rvBytes (c.ResourceVersion' + d) = minRVL m d c true by
    unfold minRVL; rw [if_neg (show ¬ m < 30 from h1), if_neg (show ¬ m < 45 from h2), if_neg (show ¬ m < 55 from h3), if_neg (by decide), if_neg (show ¬ m < 84 from h4), if_neg (show ¬ m < 98 from h5)]]
  iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
