/-
Lean-first (no Rocq counterpart). #33 S3b W3b (2026-11-23): pure laws for the proof of
`State.InMemory` (`State__InMemory.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.InMemory

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

/-- `\E` over the list from position `j`: its element `j`, then the rest. -/
theorem anyM_drop_succ {α : Type} [Inhabited α] (l : List α) (f : α → EvalM Bool) {j : Nat} (hj : j < l.length) :
    anyM (l.drop j) f = (do if (← f l[j]!) then pure true else anyM (l.drop (j + 1)) f) := by
  rw [List.drop_eq_getElem_cons hj, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

end AntCheck
end EtcdGrove
end Perennial
