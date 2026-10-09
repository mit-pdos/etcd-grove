/-
Port of election_proof/proof_Inflights__reset.v.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Inflights__reset

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

theorem tracker.Inflights.reset.wp_proof :
    tracker.Inflights.reset.spec (GF := GF) (hG := hG) := by
  intro l i
  wp_start as Hin
  iNamed Hin
  iNamed Hin
  subst Hring
  subst Hiabs
  wp_auto
  iapply HΦ
  -- `start` and `count` go to `0` and the buffer is untouched, so every
  -- conjunct of the ring invariant is an instance of the old one
  have Hok : InflightsOk (inflightsRingOf
      { iv with start' := W64 0, count' := W64 0, bytes' := W64 0 } buf) := by
    simp only [InflightsOk, inflightsRingOf, inflightsAbs] at Hinfl_ok ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Hinfl_ok
    refine ⟨by word, by word, h3, h4, ?_, ?_⟩ <;> word
  iapply ownInflights_reseal $$ Hiv Hbuf Hbuf_cap
  ipureintro
  refine ⟨Hok, ?_⟩
  simp [inflightsRingOf, inflightsAbs, inflightsReset]

end proof

end EtcdGrove
end Perennial
