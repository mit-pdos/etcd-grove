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
  obtain ⟨uents, off, ip, snap⟩ := us
  wp_start as Hpre
  iNamed Hpre
  open_unstable
  wp_auto
  cases snap with
  | some sid =>
    -- a pending snapshot: `snapshot.Metadata.Index + 1`
    icases (ownSnap_Some _ _).1 $$ Hsnap with ⟨%sv, #Hsv, %Hmeta, -⟩
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
    refine ⟨by simp, ?_⟩
    rintro _ ⟨⟩
    rw [Hmeta.1]
  | none =>
    ihave %Hns := (ownSnap_None _).1 $$ Hsnap
    wp_if_destruct
    · iapply HΦ
      isplitl
      · close_unstable
      ipureintro
      simp
    · exact absurd Hns Hif

end proof

end EtcdGrove
end Perennial
