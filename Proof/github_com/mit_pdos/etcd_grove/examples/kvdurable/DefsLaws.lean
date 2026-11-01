/-
Lean-first (no Rocq counterpart).

# Laws of the durable store's predicates (2026-11-01, durability stage II)

The persistence instances of `Defs.lean`'s persistent predicates (kvreconf's `Defs`/`DefsCluster`
instances, at kvdurable's predicates).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

instance rkvInv_persistent (γ : KdNames) : Persistent (rkvInv (GF := GF) γ) := by
  unfold rkvInv; infer_instance

instance kdSnapInv_persistent (γ : KdNames) : Persistent (kdSnapInv (GF := GF) γ) := by
  unfold kdSnapInv; infer_instance

instance isStats_persistent (s : Loc) : Persistent (isStats (GF := GF) s) := by
  unfold isStats; infer_instance

instance kdCluster_persistent (γ : KdNames) (vs : List w64) :
    Persistent (kdCluster (GF := GF) γ vs) := by
  unfold kdCluster; infer_instance

instance kdSnapCert_persistent (γ : KdNames) (sv : SnapshotM) :
    Persistent (kdSnapCert (GF := GF) γ sv) := by
  unfold kdSnapCert; infer_instance

instance kdFileInv_persistent (γ : KdNames) (dir : GoString) (id : w64) :
    Persistent (kdFileInv (GF := GF) γ dir id) := by
  unfold kdFileInv; infer_instance

instance isReadSeqs_persistent (γ : KdNames) (s : Loc) : Persistent (isReadSeqs (GF := GF) γ s) := by
  unfold isReadSeqs; infer_instance

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance isReplica_persistent (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64)
    (r n st sts sq ms : Loc) (γs : MemStorNames) (ph : GName) :
    Persistent (isReplica (GF := GF) γ vs dir id r n st sts sq ms γs ph) := by
  unfold isReplica; infer_instance

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance isReplicaR_persistent (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64)
    (r n st sts sq : Loc) (ρ : KdRepNames) :
    Persistent (isReplicaR (GF := GF) γ vs dir id r n st sts sq ρ) := by
  unfold isReplicaR; infer_instance

instance sendSpec_persistent (γ : KdNames) (id : w64) (f : GoFunc) :
    Persistent (sendSpec (GF := GF) γ id f) := by
  unfold sendSpec; infer_instance

end laws

end kvdurable
end EtcdGrove
end Perennial
