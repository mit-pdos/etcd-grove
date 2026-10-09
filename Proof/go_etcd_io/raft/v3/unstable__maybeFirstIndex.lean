/-
Port of election_proof/proof_unstable__maybeFirstIndex.v.
-/
module

public import Spec.go_etcd_io.raft.v3.unstable__maybeFirstIndex

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

theorem unstable.maybeFirstIndex.wp_proof :
    unstable.maybeFirstIndex.spec (GF := GF) (hG := hG) := by
  intro u us
  wp_start as Hpre
  iNamed Hpre
  open_unstable
  wp_auto
  rcases snap_some_or_none us.snap with ⟨sid, Hs⟩ | Hs
  · -- a pending snapshot: `snapshot.Metadata.Index + 1`
    icases ownSnap_of_eq_some Hs $$ Hsnap with ⟨%sv, #Hsv, %Hmeta, -⟩
    ihave %Hnn := typedPointsto_not_null $$ Hsv
    wp_if_destruct
    · exact absurd Hif Hnn
    iStructNamed Hsv
    iStructNamed Metadata
    wp_auto
    iapply HΦ
    isplitl
    · close_unstable
    ipureintro
    rw [Hs]
    refine ⟨by simp, ?_⟩
    rintro _ ⟨⟩
    rw [Hmeta.1]
  · ihave %Hns := ownSnap_of_eq_none Hs $$ Hsnap
    wp_if_destruct
    · iapply HΦ
      isplitl
      · close_unstable
      ipureintro
      simp [Hs]
    · exact absurd Hns Hif

end proof

end EtcdGrove
end Perennial
