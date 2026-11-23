/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/state/KeyComparator.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
variable [sync.Assumptions] [SwiftNetPkgState GF]

set_option goose.wp.extras true

theorem state.KeyComparator.wp_proof : state.KeyComparator.spec (GF := GF) := fun a b => by
  wp_start
  wp_auto
  have hne : sint.Z a ≠ sint.Z b → a ≠ b := fun h e => h (by rw [e])
  have heq : sint.Z a = sint.Z b → a = b := fun h => BitVec.eq_of_toInt_eq h
  wp_if_destruct
  · iapply HΦ; ipureintro
    have h : sint.Z b < sint.Z a := by simpa using Hif
    refine ⟨⟨fun h' => by simp at h', fun h' => by omega⟩, ⟨fun h' => by simp at h', ?_⟩⟩
    intro e; subst e; omega
  · have h1 : ¬ sint.Z b < sint.Z a := by simpa using Hif
    wp_if_destruct
    · iapply HΦ; ipureintro
      have h : sint.Z a < sint.Z b := by simpa using Hif
      refine ⟨⟨fun _ => h, fun _ => by decide⟩, ⟨fun h' => absurd h' (by decide), ?_⟩⟩
      intro e; subst e; omega
    · iapply HΦ; ipureintro
      have h2 : ¬ sint.Z a < sint.Z b := by simpa using Hif
      have : a = b := heq (by omega)
      exact ⟨⟨fun h' => by simp at h', fun h' => by omega⟩, ⟨fun _ => this, fun _ => rfl⟩⟩

end proof

end Perennial.github_com.imdea_software.swiftpaxos
