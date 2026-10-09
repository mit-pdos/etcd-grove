/- Port of election_proof/proof_unstable__maybeLastIndex.v. -/
module

public import Spec.go_etcd_io.raft.v3.unstable__maybeLastIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem unstable.maybeLastIndex.wp_proof :
    unstable.maybeLastIndex.spec (GF := GF) (hG := hG) := by
  intro u us Hnw
  wp_start as H
  iNamed H
  open_unstable
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hents
  by_cases He : us.ents = []
  · have Hz : uv.entries'.len = W64 0 := by simp [He] at Hlen; word
    rw [decide_eq_true Hz]
    wp_auto
    rcases snap_some_or_none us.snap with ⟨sid, Hs⟩ | Hs
    · -- the suffix is empty and a snapshot is pending: its index
      icases ownSnap_of_eq_some Hs $$ Hsnap with ⟨%sv, #Hsv, %Hmeta, -⟩
      ihave %Hnn := typedPointsto_not_null $$ Hsv
      rw [decide_eq_false Hnn]
      iStructNamed Hsv
      iStructNamed Metadata
      wp_auto
      iapply HΦ
      isplitl
      · close_unstable
      ipureintro
      exact ⟨fun _ => ⟨by simp [Hs], fun _ Hs' => by rw [Hs] at Hs'; cases Hs'; exact Hmeta.1⟩,
        fun Hc => absurd He Hc⟩
    · ihave %Hns := ownSnap_of_eq_none Hs $$ Hsnap
      rw [decide_eq_true Hns]
      wp_auto
      iapply HΦ
      isplitl
      · close_unstable
      ipureintro
      simp [He, Hs]
  · have Hz : uv.entries'.len ≠ W64 0 := by
      intro Hc; rw [Hc] at Hlen; cases Hc' : us.ents with
      | nil => exact He Hc'
      | cons _ _ => simp [Hc'] at Hlen; word
    rw [decide_eq_false Hz]
    wp_auto
    iapply HΦ
    isplitl
    · close_unstable
    ipureintro
    refine ⟨fun Hc => absurd Hc He, fun _ => ⟨rfl, ?_⟩⟩
    word

end proof

end EtcdGrove
end Perennial
