/-
Lean-first (no Rocq counterpart). #33 parity B1: the persistence of the run's read-only records
(`HarnessRun.lean`'s `nodeRO`, `antCluster`, `propMinter`) and a node's record out of the
cluster's (`nodeRO_lookup`), which the driver's proofs share.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section inst
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

instance nodeRO_persistent (c : Loc) (γ : AntNames) (n : Loc) (j : Fin γ.R.N) :
    Persistent (nodeRO (GF := GF) c γ n j) := by
  unfold nodeRO; infer_instance

instance propMinter_persistent (γ : AntNames) : Persistent (propMinter (GF := GF) γ) := by
  unfold propMinter; infer_instance


set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
instance antCluster_persistent (c : Loc) (γ : AntNames) : Persistent (antCluster (GF := GF) c γ) := by
  unfold antCluster; infer_instance

/-- Node `j`'s record, out of the cluster's. -/
theorem nodeRO_lookup (c : Loc) (γ : AntNames) (ns : List Loc) (j : Fin γ.R.N) :
    ([∗list] k ∈ List.finRange γ.R.N, nodeRO (GF := GF) c γ ns[k.val]! k) ⊢ nodeRO c γ ns[j.val]! j :=
  BigSepL.bigSepL_lookup (Φ := fun _ k => nodeRO (GF := GF) c γ ns[k.val]! k) (i := j.val)
    (by simp)

end inst

end AntHarness
end EtcdGrove
end Perennial
