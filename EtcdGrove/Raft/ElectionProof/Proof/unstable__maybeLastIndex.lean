/- Port of election_proof/proof_unstable__maybeLastIndex.v. -/
import EtcdGrove.Raft.ElectionProof.Spec.unstable__maybeLastIndex

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem unstable.maybeLastIndex.wp_proof :
    unstable.maybeLastIndex.spec (GF := GF) (hG := hG) := by
  intro u uv uents snap Hnw
  wp_start as H
  iNamed H
  unfold ownUnstable
  iNamed Hun
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hents
  by_cases He : uents = []
  · subst He
    have Hz : uv.entries'.len = W64 0 := by simp at Hlen; word
    rw [decide_eq_true Hz]
    wp_auto
    cases snap with
    | some sid =>
      -- the suffix is empty and a snapshot is pending: its index
      icases (ownSnap_Some _ sid).1 $$ Hsnap with ⟨%sv, #Hsv, %Hmeta, -⟩
      ihave %Hnn := typedPointsto_not_null $$ Hsv
      rw [decide_eq_false Hnn]
      iStructNamed Hsv
      iStructNamed Metadata
      wp_auto
      iapply HΦ
      iframe
      ipureintro
      exact ⟨fun _ => ⟨by simp, fun _ Hs => by cases Hs; exact Hmeta.1⟩, fun Hc => absurd rfl Hc⟩
    | none =>
      ihave %Hns := (ownSnap_None _).1 $$ Hsnap
      rw [decide_eq_true Hns]
      wp_auto
      iapply HΦ
      iframe
      ipureintro
      simp
  · have Hz : uv.entries'.len ≠ W64 0 := by
      intro Hc; rw [Hc] at Hlen; cases uents with
      | nil => exact He rfl
      | cons _ _ => simp at Hlen; word
    rw [decide_eq_false Hz]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    refine ⟨fun Hc => absurd Hc He, fun _ => ⟨rfl, ?_⟩⟩
    word

end proof

end EtcdGrove
end Perennial
