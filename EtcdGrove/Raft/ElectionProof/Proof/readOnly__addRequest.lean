/- Port of election_proof/proof_readOnly__addRequest.v.

Lean notes: Rocq's `wp_slice_append_persistent` is Perennial's
`wp_slice_append_persistent` (`Golang/Theory/Slice.lean`). -/
import EtcdGrove.Raft.ElectionProof.Spec.readOnly__addRequest

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

theorem readOnly.addRequest.wp_proof : readOnly.addRequest.spec (GF := GF) (hG := hG) := by
  intro ro r commitIndex req ents
  wp_start as Hown
  iNamed Hown
  unfold ownReadOnly
  iNamed Hown
  wp_auto
  ipersist «$sl0»
  wp_apply wp_slice_literal (V := Loc) [«$sl0_ptr»]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  wp_apply wp_slice_append_persistent (V := Loc) _ _ _ _ _ $$ [$Hucr_cap $Hucr $Hsl]
    as %s' ⟨Hs', Hcap', -⟩
  iapply HΦ
  iexists { rov with unconfirmedReads' := s' }, ptrs ++ [«$sl0_ptr»]
  simp only [readonlyAdd, named]
  iframe Hro Hacks Hs' Hcap'
  isplitr
  · ipureintro; exact Hro_safe
  isplitr
  · ipureintro; exact Hro_conf
  iapply BigSepL2.bigSepL2_snoc.2
  iframe Hreqs
  unfold ownReadreq
  iexists _
  iframe «$sl0» Hents
  ipureintro
  exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
