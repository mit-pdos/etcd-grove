/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/QuorumModel.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The pure quorum model of `QuorumPure.lean` is `Spec/swift/Model.lean`'s: `qcomb` is `combos`,
`aqOf` is `AQ`, `b % N` is `leaderOf`. Kept apart (Model.lean is being rewritten; nothing else
depends on this file).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumPure
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace replica.quorum

theorem qcomb_eq_combos (k : Nat) (l : List Nat) : qcomb k l = sp.combos k l := by
  induction l generalizing k with
  | nil => cases k <;> rfl
  | cons a l ih =>
    cases k with
    | zero => rfl
    | succ k => simp only [qcomb, sp.combos, ih]

theorem aqOf_eq_AQ (N b : Nat) : aqOf N b = sp.AQ N b := by
  unfold aqOf numAQ lqs quorums sp.AQ sp.leaderOf
  rw [qcomb_eq_combos]

end replica.quorum

end Perennial.github_com.imdea_software.swiftpaxos

end
