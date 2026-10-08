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
  unfold ownInflights
  icases Hin with ⟨%iv, %buf, Hin⟩
  iNamed Hin
  unfold ownInflightsRaw
  iNamed Hin
  wp_auto
  iapply HΦ
  iexists { iv with start' := W64 0, count' := W64 0, bytes' := W64 0 }, buf
  simp only [named]
  iframe
  ipureintro
  constructor
  · -- `start` and `count` go to `0` and the buffer is untouched, so every
    -- conjunct of the ring invariant is an instance of the old one
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Hinfl_ok
    unfold InflightsOk
    simp only
    refine ⟨by word, by word, h3, h4, ?_, ?_⟩ <;> word
  · subst Hiabs
    simp [inflightsAbs, inflightsReset]

end proof

end EtcdGrove
end Perennial
