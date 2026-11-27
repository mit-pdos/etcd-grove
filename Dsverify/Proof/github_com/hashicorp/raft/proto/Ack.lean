/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/Ack.lean (241f27e).
-/
/-
`proto` — `ack` preserves `PInv` (leader completeness of a newly committed prefix is `ILC_of`:
the acknowledging server cannot have voted in a later term).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.Frame

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

theorem ack_inv' (σ : PState) (i : SID) (k : Nat) (h : PInv σ) (hp : ackPre σ i k) :
    PInv (ack σ i (σ.term i) k) ∧ Grows σ (ack σ i (σ.term i) k) := by
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  obtain ⟨hi, hld, hag⟩ := hp
  have hg : HG σ (ack σ i (σ.term i) k) := HG.refl_llog rfl rfl rfl rfl rfl
  have hack : ∀ j T m, σ.acked j T m → (ack σ i (σ.term i) k).acked j T m :=
    fun j T m x => Or.inl x
  have hA' : IAcks (ack σ i (σ.term i) k) := by
    intro j T m ha
    rcases ha with ha | ⟨rfl, rfl, rfl⟩
    · exact hA j T m ha
    · exact ⟨hi, hld, hag.2.1, Nat.le_refl _, fun k' hk' => Or.inl (agree_mono hag hk')⟩
  have hVA' : IVoteAck (ack σ i (σ.term i) k) := by
    intro j T' c L b T m k' hv ha hkm hTT'
    rcases ha with ha | ⟨rfl, rfl, rfl⟩
    · exact hVA j T' c L b T m k' hv ha hkm hTT'
    · have a := (hV.1 j T' c L b hv).2.2.1
      have b := (hV.2.1 j hi).1
      exact absurd hTT' (by omega)
  have hCo' : ICommits (ack σ i (σ.term i) k) :=
    ICommits_grow hg hack (fun _ _ _ => Iff.rfl) rfl hCo
  refine ⟨⟨hG, hL, hLo, hC, hV, hA', hVA',
    ILC_of (σ := ack σ i (σ.term i) k) hG hL hLo hV hVA' hR
      (fun T k p h => ⟨(hCo'.1 T k p h).1, (hCo'.1 T k p h).2.1⟩),
    hCo', hD, hB, hX, hP, hR⟩, ?_⟩
  exact ⟨rfl, ⟨rfl, rfl⟩, fun _ _ x => x, fun T => ⟨List.prefix_refl _, fun _ => rfl⟩,
      fun _ _ _ x => x, fun _ _ _ x => x, hack, fun _ _ _ x => x, List.prefix_refl _,
      fun _ => Nat.le_refl _, fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ _ x => x,
      fun _ _ _ _ x => Or.inl x⟩

end proto
end github_com.hashicorp.raft
end Perennial
