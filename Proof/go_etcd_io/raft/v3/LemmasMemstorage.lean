/-
Lemmas of the `MemoryStorage` proofs (raft v3.7 retarget, stage R3): reading the storage's entry
slice (`entsRO`, `InvPbLog.lean`) at a position.
-/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage
public import Proof.go_etcd_io.raft.v3.LemmasEnts

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- A conf state whose lists and `AutoLeave` are the storage's is `storCS σ`. -/
theorem confState_eq_storCS [GooseExts] (c : ConfStateM) (σ : StorState) (h1 : c.lists = σ.scs)
    (h2 : c.AutoLeave' = σ.sal) : c = storCS σ := by
  unfold storCS
  rw [← h1, ← h2]
  rfl


end EtcdGrove
end Perennial
