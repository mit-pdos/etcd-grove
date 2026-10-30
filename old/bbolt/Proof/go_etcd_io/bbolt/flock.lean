module
public import Spec.go_etcd_io.bbolt.flock
public import Spec.os.File__Fd
public import Spec.syscall.Flock
public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem flock.wp_proof (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hFlock : syscall.Flock.spec (GF := GF) (hG := hG)) :
    flock.spec (GF := GF) (hG := hG) := by
  intro dbl f fd dq ex tmo
  wp_start as ⟨Hf, #Hof⟩
  ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
  · iPkgInit
  icases bboltError_access errors.ErrTimeout (by simp [bboltErrorNames]) $$ Hei
    with ⟨%e, #He, %Hne⟩
  wp_auto
  wp_if_destruct
  all_goals try (wp_apply time.wp_Now as %t0 -)
  all_goals try wp_auto
  all_goals
    wp_apply hFd f fd $$ [Hof]
    · iexact Hof
    try wp_auto
    wp_if_destruct
    all_goals
      try rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true rfl))]
      try rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp))]
      try wp_auto
      ihave IH : iprop(∃ (fl : w64) (tv : time.Time) (tm : w64), "fd" ∷ fd_ptr ↦ fd ∗
          "flag" ∷ flag_ptr ↦ fl ∗ "t" ∷ t_ptr ↦ tv ∗ "timeout" ∷ timeout_ptr ↦ tm ∗
          "Hf" ∷ structFieldRef DB go!"file" dbl ↦{dq} f) $$ [fd flag t timeout Hf]
      · iexists _, _, _; iframe
      wp_for IH
      try rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true rfl))]
      try wp_auto
      wp_apply hFlock as %err %Herr
      try wp_auto
      rcases Herr with rfl | ⟨eno, rfl⟩
      · try wp_auto
        wp_for_post
        iapply HΦ; iframe
      · try wp_auto
        wp_if_destruct
        all_goals try wp_auto
        all_goals try (wp_for_post; iapply HΦ; iframe; done)
        all_goals try wp_if_destruct
        all_goals try (wp_apply time.wp_Since as %d -)
        all_goals try wp_auto
        all_goals try wp_if_destruct
        all_goals try wp_auto
        all_goals try (wp_for_post; iapply HΦ; iframe; done)
        all_goals
          wp_apply time.wp_Sleep
          try wp_auto
          wp_for_post
          iframe
          iexists _, _, _
          iframe

end proof

end bbolt
end EtcdGrove
end Perennial
