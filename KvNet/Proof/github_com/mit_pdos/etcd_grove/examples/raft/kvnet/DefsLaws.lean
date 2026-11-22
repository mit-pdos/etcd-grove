/-
(kvnet's own: kvdurablenoax's `DefsLaws.lean` without the laws of the definitions kvnet's
`Defs.lean` does not have: `repKnown`, `isStats` (kvnet's is `TransportDefs.lean`'s), `kdFileInv`,
`isReadSeqs`, `isClusterC`, `sendSpec`.)

Lean-first (no Rocq counterpart).

# Laws of the durable store's predicates (2026-11-01, durability stage II)

The persistence instances of `Defs.lean`'s persistent predicates (kvreconf's `Defs`/`DefsCluster`
instances, at kvdurable's predicates).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

instance kvCore_timeless (γ : KdNames) (ops : List LogEntry) (n : w64) (Mi : GMap w64 (List w8))
    (RS : GMap w64 w64) (RMi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName))
    (U : GSet (List w8)) : Timeless (kvCore (GF := GF) γ ops n Mi RS RMi O U) := by
  unfold kvCore; infer_instance

instance waitP_persistent (γ : KdNames) (d v : List w8) : Persistent (waitP (GF := GF) γ d v) := by
  unfold waitP; infer_instance

instance kvLb_persistent (γ : KdNames) (L : List (List w8)) : Persistent (kvLb (GF := GF) γ L) := by
  unfold kvLb; infer_instance

instance rsOk_persistent (γ : Cluster) (v : ReadState) : Persistent (rsOk (GF := GF) γ v) := by
  unfold rsOk; infer_instance

instance readAns_persistent (γ : KdNames) (c v : List w8) : Persistent (readAns (GF := GF) γ c v) := by
  unfold readAns; infer_instance

instance kdSnapRecOk_persistent (γ : KdNames) (s : SnapRec) :
    Persistent (kdSnapRecOk (GF := GF) γ s) := by
  unfold kdSnapRecOk; infer_instance

instance rkvInv_persistent (γ : KdNames) : Persistent (rkvInv (GF := GF) γ) := by
  unfold rkvInv; infer_instance

instance kdSnapInv_persistent (γ : KdNames) : Persistent (kdSnapInv (GF := GF) γ) := by
  unfold kdSnapInv; infer_instance

instance kdCluster_persistent (γ : KdNames) (vs : List w64) :
    Persistent (kdCluster (GF := GF) γ vs) := by
  unfold kdCluster; infer_instance

instance kdSnapCert_persistent (γ : KdNames) (sv : SnapshotM) :
    Persistent (kdSnapCert (GF := GF) γ sv) := by
  unfold kdSnapCert; infer_instance

instance fileHolds_persistent (γ : KdNames) (S : RaftState) (v : Option GoString) :
    Persistent (fileHolds (GF := GF) γ S v) := by
  unfold fileHolds; infer_instance

instance sendSpec_persistent (γ : KdNames) (id : w64) (f : GoFunc) :
    Persistent (sendSpec (GF := GF) γ id f) := by
  unfold sendSpec; infer_instance

instance kdFileInvK_persistent (γ : KdNames) (id : w64) (fl : KdFileNames) :
    Persistent (kdFileInvK (GF := GF) γ id fl) := by
  unfold kdFileInvK; infer_instance

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance isReplica_persistent (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64)
    (r : Loc) (n : NodeH) (st sts sq ms : Loc) (γs : MemStorNames) (ph : KdDmuNames) :
    Persistent (isReplica (GF := GF) γ vs dir id r n st sts sq ms γs ph) := by
  unfold isReplica; infer_instance

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance isReplicaR_persistent (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64)
    (r : Loc) (n : NodeH) (st sts sq : Loc) (ρ : KdRepNames) :
    Persistent (isReplicaR (GF := GF) γ vs dir id r n st sts sq ρ) := by
  unfold isReplicaR; infer_instance

instance isRep_persistent (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc) :
    Persistent (isRep (GF := GF) γ vs dir id r) := by
  unfold isRep; infer_instance

/-- Three halves of a ghost variable are refuted. -/
theorem ghostVar_three_halves {A : Type} [Pos.Countable A] (γv : GName) (a b c : A) :
    ghostVar (GF := GF) γv (1 : Qp).half a ∗ ghostVar γv (1 : Qp).half b ∗
      ghostVar γv (1 : Qp).half c ⊢ False := by
  iintro ⟨H1, H2, H3⟩
  ihave %Hab := ghostVar_agree γv _ _ _ _ $$ H1 H2
  subst Hab
  ihave H12 : ghostVar γv ((1 : Qp).half + (1 : Qp).half) a $$ [H1 H2]
  · iapply (ghostVar_fractional (GF := GF) γv a).fractional _ _ |>.2
    iframe H1 H2
  rw [Qp.half_add_half] at *
  ihave %Hv := ghostVar_valid_2 γv _ _ _ _ $$ H12 H3
  exfalso
  have h1 : (1 : Rat) + ((1 : Qp).half).val ≤ 1 := Hv.1
  have := ((1 : Qp).half).2
  grind

/-- The replica's file's namespace is not the files'. -/
theorem kdRepN_files (id : w64) : (↑(kdRepN .@ uint.nat id) : CoPset) ⊆ ⊤ \ ↑kdFilesN :=
  nclose_subseteq' _ (mask_ndot_ne' nroot "kvdurable_rep" "kvdurable_files" (by decide))

/-- The replica's file's namespace is not raft's. -/
theorem kdRepN_raft (id : w64) : (↑(kdRepN .@ uint.nat id) : CoPset) ⊆ ⊤ \ ↑kdRaftN :=
  nclose_subseteq' _ (mask_ndot_ne' nroot "kvdurable_rep" "kvdurable_raft" (by decide))

/-- (2026-11-22) The replica's file's namespace is open inside `durable`'s atomic updates. -/
theorem kdRepN_sub_durAu (id : w64) : (↑(kdRepN .@ uint.nat id) : CoPset) ⊆ DurFs.durAuMask := by
  intro x hx
  have h1 := nclose_subseteq' _ (mask_ndot_ne' nroot "kvdurable_rep" "osfs" (by decide)) x hx
  have h2 := nclose_subseteq' _ (mask_ndot_ne' nroot "kvdurable_rep" "osfsShared" (by decide)) x hx
  have h3 := nclose_subseteq' _ (mask_ndot_ne' nroot "kvdurable_rep" "durable" (by decide)) x hx
  rw [Std.LawfulSet.mem_diff] at h1 h2 h3
  unfold DurFs.durAuMask Fs.osAuMask
  rw [Std.LawfulSet.mem_diff, Std.LawfulSet.mem_diff, Std.LawfulSet.mem_diff]
  exact ⟨⟨⟨CoPset.mem_full, h1.2⟩, h2.2⟩, h3.2⟩

/-- (2026-11-22) Raft's namespace is open inside `durable`'s atomic updates with the file's invariant
open. -/
theorem kdRaftN_sub_durAu (id : w64) :
    (↑kdRaftN : CoPset) ⊆ DurFs.durAuMask \ ↑(kdRepN .@ uint.nat id) := by
  intro x hx
  have h1 := mask_ndot_ne' nroot "kvdurable_raft" "osfs" (by decide) x hx
  have h2 := mask_ndot_ne' nroot "kvdurable_raft" "osfsShared" (by decide) x hx
  have h3 := mask_ndot_ne' nroot "kvdurable_raft" "durable" (by decide) x hx
  have h4 := nclose_subseteq' (uint.nat id) (mask_ndot_ne' nroot "kvdurable_rep" "kvdurable_raft" (by decide))
  rw [Std.LawfulSet.mem_diff] at h1 h2 h3
  unfold DurFs.durAuMask Fs.osAuMask
  rw [Std.LawfulSet.mem_diff, Std.LawfulSet.mem_diff, Std.LawfulSet.mem_diff, Std.LawfulSet.mem_diff]
  refine ⟨⟨⟨⟨CoPset.mem_full, h1.2⟩, h2.2⟩, h3.2⟩, fun h => ?_⟩
  have := h4 x h
  rw [Std.LawfulSet.mem_diff] at this
  exact this.2 hx

end laws

end raft_kvnet
end EtcdGrove
end Perennial
