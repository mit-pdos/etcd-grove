/-
premcheck's validation on paxos: the non-vacuity instance of the empty `KitLibs` (paxos's statement
has no premise; PremCheckTest/paxos/KitLibs.lean is the challenge's template as exported).
-/
module

public import PremCheckTest.paxos.Statement

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.xiang90.paxos.examples.paxosnet

/-- The non-vacuity instance: the class is empty. -/
theorem kitLibs_nonvacuity : kitLibs.premise := by
  unfold kitLibs.premise
  intros
  exact ⟨⟩

end github_com.xiang90.paxos.examples.paxosnet
end Perennial
