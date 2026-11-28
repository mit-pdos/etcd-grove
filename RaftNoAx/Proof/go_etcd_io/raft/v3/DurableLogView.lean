-- The copy for the part `RaftNoAx/` of `Proof/go_etcd_io/raft/v3/DurableLogView.lean` (etc/copy-part.py; rerun it, do not edit).
/- Observe the retained entries and committed prefix while keeping ownership of the durable state. -/
module
public import RaftNoAx.Proof.go_etcd_io.raft.v3.InvNodeRule
import RaftNoAx.Proof.go_etcd_io.raft.v3.LogEntryOrder
import all RaftNoAx.Proof.go_etcd_io.raft.v3.InvNodeRule
import all RaftNoAx.Proof.go_etcd_io.raft.v3.InvNode
import RaftNoAx.Proof.go_etcd_io.raft.v3.InvApi
import RaftNoAx.Proof.go_etcd_io.raft.v3.InvApiDec

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
/-- (keepfix (c), 2026-11-27) **A node's durable state certifies its own commit index at its own
term**: the log through `S.commit` was committed at a term `≤ S.term` (`committedAtTerm`), with the
durable state kept. What etcd's boot seed (`bootOkR`'s `srvCITriple`) needs of the hard state raft
restarts from (`~/coordinator-notes/plans/keepfix-c-design.md`, §0). From `durPers`'s
`commitIn (fp ++ S.ents) S.commit S.term` and its committed prefix. -/
theorem raftState_committedAtTerm (γ : Cluster) (id : w64) (S : RaftState) (N : Namespace)
    (Em : CoPset) (hEm : ↑N ⊆ Em) :
    isCluster (GF := GF) γ N ∗ raftState γ id S ⊢ |={Em}=>
      raftState γ id S ∗ committedAtTerm γ N S.term S.commit := by
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
  icases Hfacts with ⟨%kd, %fp, %hf, #Hents, -, #Hpre, -, -, -, -, #HcIn, #Hcommit, -⟩
  obtain ⟨-, -, -, -, hfull, hwf, -, -, -⟩ := hf
  ihave #Hlog := logRecs_full (ApiImpl.Cluster.raft γ) S.base fp S.ents hfull $$ Hpre Hents
  have hfw := full_wf S.base fp S.ents hfull hwf
  ihave #Hw : commitWit (GF := GF) (ApiImpl.Cluster.raft γ) S.term S.commit $$ []
  · unfold commitWit
    iexists fp ++ S.ents
    iframe Hlog HcIn Hcommit
    ipureintro; exact hfw
  imod ApiImpl.committedAtTerm_of_raft γ N Em hEm S.term S.commit $$ Hci Hw Hterm with Hcat
  imodintro
  isplitl [Hshares Hslot Hi1]
  · iunfold raftState
    iunfold ApiImpl.raftStateU
    iframe Hterm Hbudget
    iunfold ownDurGhost
    iexists E
    iframe Hshares Hpers Hslot Hi1
  iunfold committedAtTerm
  iexact Hcat

omit [StorageModel GF] in
/-- (keepfix (c), 2026-11-27) Every entry of a log with records has a term `≥ 1`, once the
bootstrap log is non-empty (`isEntryR_term_pos`). -/
theorem logRecs_terms_pos (γ : RaftNames) (G : List EntryM) (Hwf : PlogWf base0 G)
    (hb : γ.reBoot ≠ []) :
    logRecs (GF := GF) γ base0 G ⊢ ⌜∀ (k : Nat) (x : EntryM), G[k]? = some x → 1 ≤ uint.Z x.Term'⌝ := by
  refine (BI.forall_intro fun k => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun x => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun Hk => ?_).trans BI.pure_forall.2
  have Hi := Hwf k x Hk
  have Hr := uint_Z_lt x.Index'
  iintro #H
  icases logRecs_lookup γ G k x Hk (by rw [base0_index] at Hi; push_cast at Hi; omega) $$ H
    with ⟨%pt, -, #He⟩
  icases isEntryR_term_pos γ x pt $$ He with %Hp
  ipureintro; exact Hp hb

omit [StorageModel GF] in
/-- (keepfix (c), 2026-11-27) **Every entry of a committed log has a nonzero term** (in a cluster
started from a non-empty bootstrap log): the committed log is the bootstrap log (every entry's term
`1`) or a prefix of a commit quorum's leader log, whose entries have records (`isEntryR_term_pos`).
Through the cluster's invariant (`api_committed_cert`). -/
theorem isCommittedLogLb_term_pos (γ : Cluster) (N : Namespace) (l : List LogEntry) (Em : CoPset)
    (hEm : ↑N ⊆ Em) (hb : 0 < γ.bootLen) :
    isCluster (GF := GF) γ N ∗ isCommittedLogLb γ l ⊢ |={Em}=> ⌜∀ e ∈ l, 1 ≤ uint.Z e.term⌝ := by
  have hb' : (ApiImpl.Cluster.raft γ).reBoot ≠ [] := by
    unfold Cluster.bootLen at hb; exact List.length_pos_iff.mp hb
  iintro ⟨#Hcluster, #Hlb⟩
  iunfold isCluster at Hcluster
  iunfold ApiImpl.isClusterU at Hcluster
  icases Hcluster with ⟨-, #Hci, -⟩
  iunfold isCommittedLogLb at Hlb
  imod ApiImpl.api_committed_cert γ N Em hEm l $$ Hci Hlb with (%Hl | ⟨%P, %HP, -, Hcase⟩)
  · imodintro; ipureintro; subst Hl; intro e he; simp at he
  obtain ⟨Hpre, -⟩ := HP
  -- every entry of `P` has a term `≥ 1`
  ihave %HPt : ⌜∀ (k : Nat) (x : EntryM), P[k]? = some x → 1 ≤ uint.Z x.Term'⌝ $$ [Hcase]
  · icases Hcase with (%Hb | ⟨%t, %n, %G, %ldr, #Hcq, %HPG, -⟩)
    · obtain ⟨HPb, -, Hones⟩ := Hb
      ipureintro; intro k x Hk
      rw [HPb] at Hk
      rw [Hones x (List.mem_of_getElem? Hk)]; word
    · icases cq_full _ t n G $$ Hcq with ⟨%Hwf, #Hr⟩
      icases logRecs_terms_pos _ G Hwf hb' $$ Hr with %HG
      ipureintro; intro k x Hk
      rw [HPG, List.getElem?_take] at Hk
      split at Hk
      · exact HG k x Hk
      · simp at Hk
  imodintro
  ipureintro
  intro e he
  obtain ⟨r, hr⟩ := Hpre
  have he' : e ∈ strip P := by rw [← hr]; exact List.mem_append_left _ he
  simp only [strip, List.mem_map] at he'
  obtain ⟨x, hx, rfl⟩ := he'
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
  exact HPt k x (by rw [List.getElem?_eq_getElem hk, hkx])

theorem raftState_logView (γ : Cluster) (id : w64) (S : RaftState) (N : Namespace) :
    isCluster (GF := GF) γ N ∗ raftState γ id S ⊢ |={⊤}=>
      raftState γ id S ∗ ∃ fp : List EntryM,
        ⌜FullOk S.base fp ∧ PlogWf S.base S.ents ∧ uint.nat S.commit ≤ (fp ++ S.ents).length⌝ ∗
        ⌜(fp ++ S.ents).Pairwise (fun a b => uint.nat a.Term' ≤ uint.nat b.Term' ∧ uint.nat a.Index' < uint.nat b.Index')⌝ ∗
        isCommittedLogLb γ (strip ((fp ++ S.ents).take (uint.nat S.commit))) :=
  raftState_logViewE γ id S N ⊤ CoPset.subseteq_top

end EtcdGrove
end Perennial
