/-
Proof of `Spec/google_golang_org/grpc/chainUnaryServerInterceptors.lean` over the model's body (W1,
2026-11-26): no single `unaryInt` to prepend; then by the chain's length.
-/
module

public import Spec.google_golang_org.grpc.chainUnaryServerInterceptors
public import Spec.google_golang_org.grpc.chainUnaryInterceptors

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
variable [package_sem : google_golang_org.grpc.Assumptions]

theorem grpc.chainUnaryServerInterceptors.wp_proof
    (wp_chainUnaryInterceptors : grpc.chainUnaryInterceptors.spec (GF := GF) (hG := hG)) :
    grpc.chainUnaryServerInterceptors.spec (GF := GF) (hG := hG) := by
  intro gs so ics
  wp_start as ⟨Hopts, #Hics, %Hui⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hics
  obtain ⟨Hl1, Hl2⟩ := Hlen
  wp_auto
  -- `s.opts.unaryInt != nil`: it is nil
  wp_if_destruct <;>
    try (exfalso; first | exact Hif Hui | exact Hif (Hui.trans rfl) | (simp_all; done))
  -- the chained interceptor, by the chain's length
  wp_if_destruct
  · -- none: nil
    have hnil : ics = [] := List.eq_nil_of_length_eq_zero (by rw [Hl1, Hif]; try rfl)
    iapply HΦ
    isplitl [Hopts]
    · iexact Hopts
    unfold srvChainIs
    isplitr
    · iexact Hics
    ileft
    ipureintro
    exact ⟨hnil, rfl⟩
  · have H0 := Hif
    wp_if_destruct
    · -- one: it
      obtain ⟨i, rfl⟩ := List.length_eq_one_iff.1 (show ics.length = 1 by rw [Hl1, Hif]; try rfl)
      have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z so.chainUnaryInts'.len := by
        rw [Hif]; decide
      (try simp only [Hbnd, _root_.and_self, ite_true])
      wp_apply (wp_load_slice_index so.chainUnaryInts' (sint.Z (W64 0)) [i] DFrac.discard i
        (by decide)) $$ [$Hics] as -
      · ipureintro; rfl
      iapply HΦ
      isplitl [Hopts]
      · iexact Hopts
      unfold srvChainIs
      isplitr
      · iexact Hics
      iright
      ileft
      iexists i
      ipureintro
      exact ⟨rfl, rfl⟩
    · -- two or more: the chaining closure
      have H1 := Hif
      wp_apply (wp_chainUnaryInterceptors so.chainUnaryInts') as %il #Hil
      iapply HΦ
      isplitl [Hopts]
      · iexact Hopts
      unfold srvChainIs
      isplitr
      · iexact Hics
      iright
      iright
      iexists il
      isplitr
      · ipureintro
        exact ⟨by rw [Hl1]; word, rfl⟩
      iexact Hil

end proof

end EtcdGrove
end Perennial
