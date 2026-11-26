/-
Proof of `Spec/google_golang_org/grpc/internal/stats/NewCombinedHandler.lean` over the model's body
(W1, 2026-11-26): the `switch len(handlers)`.
-/
module

public import Spec.google_golang_org.grpc.internal.stats.NewCombinedHandler

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.internal.stats.Assumptions]

theorem istats.NewCombinedHandler.wp_proof :
    istats.NewCombinedHandler.spec (GF := GF) (hG := hG) := by
  intro sl hs
  wp_start as #Hsl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  obtain ⟨Hl1, Hl2⟩ := Hlen
  iapply wp_fupd
  wp_auto
  wp_if_destruct
  · -- no handler: `nil`
    have hnil : hs = [] := List.eq_nil_of_length_eq_zero (by rw [Hl1, Hif]; try rfl)
    imodintro
    iapply HΦ
    ileft
    ipureintro
    exact ⟨hnil, rfl⟩
  · have H0 := Hif
    wp_if_destruct
    · -- one: it
      obtain ⟨h, rfl⟩ := List.length_eq_one_iff.1 (show hs.length = 1 by rw [Hl1, Hif]; try rfl)
      have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by rw [Hif]; decide
      (try simp only [Hbnd, _root_.and_self, ite_true])
      wp_apply (wp_load_slice_index sl (sint.Z (W64 0)) [h] DFrac.discard h (by decide))
        $$ [$Hsl] as -
      · ipureintro; rfl
      imodintro
      iapply HΦ
      iright
      ileft
      iexists h
      ipureintro
      exact ⟨rfl, rfl⟩
    · -- more: a `*combinedHandler` holding the slice
      have H1 := Hif
      wp_alloc l as Hl
      (try wp_auto)
      ipersist Hl
      imodintro
      iapply HΦ
      iright
      iright
      iexists l
      isplitr
      · ipureintro
        exact ⟨by rw [Hl1]; word, rfl⟩
      iexact Hl

end proof

end EtcdGrove
end Perennial
