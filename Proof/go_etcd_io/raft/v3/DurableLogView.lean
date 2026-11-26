/- Observe the retained entries and committed prefix while keeping ownership of the durable state. -/
module
public import Proof.go_etcd_io.raft.v3.InvNodeRule
import Proof.go_etcd_io.raft.v3.LogEntryOrder
import all Proof.go_etcd_io.raft.v3.InvNodeRule
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiDec

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics] [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (P5 (b), 2026-11-26) `raftState_logView` at any mask holding the cluster's namespace (the server's
crash law and *enter* run inside its own invariant). -/
theorem raftState_logViewE (γ : Cluster) (id : w64) (S : RaftState) (N : Namespace) (Em : CoPset)
    (hEm : ↑N ⊆ Em) :
    isCluster (GF := GF) γ N ∗ raftState γ id S ⊢ |={Em}=>
      raftState γ id S ∗ ∃ fp : List EntryM,
        ⌜FullOk S.base fp ∧ PlogWf S.base S.ents ∧ uint.nat S.commit ≤ (fp ++ S.ents).length⌝ ∗
        ⌜(fp ++ S.ents).Pairwise (fun a b => uint.nat a.Term' ≤ uint.nat b.Term' ∧ uint.nat a.Index' < uint.nat b.Index')⌝ ∗
        isCommittedLogLb γ (strip ((fp ++ S.ents).take (uint.nat S.commit))) := by
  iintro ⟨#Hcluster, Hstate⟩
  iunfold isCluster at Hcluster
  iunfold ApiImpl.isClusterU at Hcluster
  icases Hcluster with ⟨-, #Hci, -⟩
  iunfold raftState at Hstate
  iunfold ApiImpl.raftStateU at Hstate
  icases Hstate with ⟨Hdur, #Hterm, #Hbudget⟩
  iunfold ownDurGhost at Hdur
  icases Hdur with ⟨%E, Hshares, #Hpers, Hslot, Hi1⟩
  ihave #Hfacts := Hpers
  iunfold durPers at Hfacts
  icases Hfacts with ⟨%kd, %fp, %hf, #Hents, -, #Hpre, -, -, -, -, -, #Hcommit, -⟩
  obtain ⟨-, -, -, -, hfull, hwf, -, -, hmax⟩ := hf
  ihave #Hlog := logRecs_full (ApiImpl.Cluster.raft γ) S.base fp S.ents hfull $$ Hpre Hents
  have hfw := full_wf S.base fp S.ents hfull hwf
  ihave %horder := logRecs_entryOrder (ApiImpl.Cluster.raft γ) _ hfw $$ Hlog
  have hc : (uint.Z S.commit).toNat = uint.nat S.commit := by word
  isimp only [hc] at Hcommit
  imod ApiImpl.api_committed_lb γ N Em hEm
      ((fp ++ S.ents).take (uint.nat S.commit)) $$ Hci Hcommit with ⟨Hlb, -⟩
  imodintro
  isplitl [Hshares Hslot Hi1]
  · iunfold raftState
    iunfold ApiImpl.raftStateU
    iframe Hterm Hbudget
    iunfold ownDurGhost
    iexists E
    iframe Hshares Hpers Hslot Hi1
  iexists fp
  iunfold isCommittedLogLb
  iframe Hlb
  isplitl []
  rotate_left
  · ipureintro; exact horder
  ipureintro
  refine ⟨hfull, hwf, ?_⟩
  have hlen := hfull.1
  unfold plogLastIndexZ at hmax
  simp only [List.length_append]
  have := uint_nat_eq S.commit
  omega
theorem raftState_logView (γ : Cluster) (id : w64) (S : RaftState) (N : Namespace) :
    isCluster (GF := GF) γ N ∗ raftState γ id S ⊢ |={⊤}=>
      raftState γ id S ∗ ∃ fp : List EntryM,
        ⌜FullOk S.base fp ∧ PlogWf S.base S.ents ∧ uint.nat S.commit ≤ (fp ++ S.ents).length⌝ ∗
        ⌜(fp ++ S.ents).Pairwise (fun a b => uint.nat a.Term' ≤ uint.nat b.Term' ∧ uint.nat a.Index' < uint.nat b.Index')⌝ ∗
        isCommittedLogLb γ (strip ((fp ++ S.ents).take (uint.nat S.commit))) :=
  raftState_logViewE γ id S N ⊤ CoPset.subseteq_top

end EtcdGrove
end Perennial
