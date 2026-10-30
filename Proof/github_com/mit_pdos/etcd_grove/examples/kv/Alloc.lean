/-
Lean-first (no Rocq counterpart).

# Allocating the store's ghost state (2026-10-10)

What a cluster's set-up gives the replicas' `NewStorage` and `New`:

* `kvStorInv_alloc`: the storage registry's invariant, from the authority of an empty
  ghost map at the registry's name (allocated first, `ghost_map_alloc_empty`, and made the
  `KVStor` instance).
* `rkvInv_alloc`: the store's invariant over raft's cluster, from what the cluster's allocation
  (`cluster_alloc`) hands the client -- the committed requested entries (none) and the
  read contexts (none used) -- with the client's half of the value (the empty store, `kvEmpty`)
  and the replicas' sequence-number tokens at `S0` (for `New`, each at 0).
* `kvCluster_alloc` (2026-10-30, stage F of the client repair): the whole cluster -- raft's
  (`cluster_alloc` of the voters, no boot log, `dup = false`), its decision authority
  (`confPolicy_alloc` at `kvConfN`), the registry of the snapshots made (`kvSnapInv_alloc`) and the
  store's invariant (`rkvInv_alloc`) -- with the founders' tokens each node's `RestartNode` takes
  (`joinAuth` is dropped: the store adds no node).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Reconf

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- The storage registry's invariant, with no storage registered yet. -/
theorem kvStorInv_alloc (E : CoPset) :
    ⊢ ghostMapAuth (KVStor.kvStorName (GF := GF)) 1 (∅ : GMap Loc KVStorRecT) ={E}=∗
      kvStorInv (GF := GF) := by
  iintro Ha
  unfold kvStorInv
  iapply inv_alloc
  inext
  unfold kvStorInvBody
  iexists ∅
  iframe Ha
  iapply BigSepM.bigSepM_empty.2
  itrivial

/-- The store's invariant over raft's cluster `γ`, from what its allocation hands the client
(`cluster_alloc`): the committed requested entries, none, and the read contexts, none
used; with the client's half of the value and the sequence-number tokens of `S0` (`New` takes
`id ↪[γr.seq] 0`). -/
theorem rkvInv_alloc (E : CoPset) (γ : Cluster) (S0 : GMap w64 w64) :
    ⊢ ownCommittedOps (GF := GF) γ [] -∗ ownReadCtxs γ ∅ ={E}=∗
      ∃ γr : RKVNames, ⌜γr.cluster = γ⌝ ∗ rkvInv γr ∗ rkvVal γr kvEmpty ∗
        [∗map] id ↦ s ∈ S0, id ↪[γr.seq] s := by
  iintro Hops HU
  imod ghostVar_alloc (GF := GF) ([] : List (List w8)) with ⟨%γv, Hv⟩
  icases ghostVar_halves γv ([] : List (List w8)) $$ Hv with ⟨Hv1, Hv2⟩
  imod ghost_map_alloc (GF := GF) S0 with ⟨%γs, HS, Hels⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64 × w64) (V := List w8) with ⟨%γm, HMi⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := GName × GName) with ⟨%γo, HO⟩
  imod inv_alloc rkvN E (rkvInvBody (GF := GF) ⟨γ, γv, γs, γm, γo⟩)
    $$ [Hops Hv1 HU HS HMi HO] with #Hinv
  · inext
    unfold rkvInvBody
    iexists [], _, ∅, ∅, ∅
    isplitl
    · unfold kvCore
      simp only [show logHist ([] : List LogEntry) = [] from rfl]
      iframe Hops Hv1 HU HS HMi HO
      ipureintro
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · intro i s d h; simp at h
      · intro d γp h; simp at h
      · intro c h; rw [GMap.elem_of_gset] at h; simp at h
      · intro d h; simp at h
      · intro e h; simp at h
    · iapply BigSepM.bigSepM_empty.2
      itrivial
  imodintro
  iexists ⟨γ, γv, γs, γm, γo⟩
  isplitr
  · ipureintro; rfl
  unfold rkvInv rkvVal
  iframe Hinv Hels
  iexists []
  iframe Hv2
  ipureintro; rfl

/-- **The store's cluster** (see the file header): from the time receipts' bound (`cluster_alloc`'s
premise), the store's cluster `kvCluster`, its invariant, the client's half at the empty store, the
sequence-number tokens of `S0`, `γ.dup = false`, and each voter's founder token. -/
theorem kvCluster_alloc (E : CoPset) (S0 : GMap w64 w64) (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) :
    ⊢ |={E}=> ∃ γr : RKVNames, ⌜γr.cluster.dup = false⌝ ∗ kvCluster γr ∗ rkvInv γr ∗
        rkvVal γr kvEmpty ∗ ([∗map] id ↦ s ∈ S0, id ↪[γr.seq] s) ∗
        [∗list] id ∈ kvVoters, nodeFounder γr.cluster kvRaftN kvVoters id := by
  iintro
  imod cluster_alloc (GF := GF) kvRaftN kvVoters [] [] false E Hrb (by decide) (by decide)
      (by decide) (by decide) (fun h => absurd rfl h) $$ [] with
    ⟨%γ, %Hγ, Hops, HU, #Hiscl, Hdec, #Hca0, Hsm, Hrest⟩
  · iempintro
  have Hif : (if ([] : List LogEntry) = [] then
      iprop(joinAuth γ (GMap.listToSet kvVoters) ∗
        [∗list] id ∈ kvVoters, nodeFounder (GF := GF) γ kvRaftN kvVoters id)
    else iprop(isCommittedLogLb γ [] ∗ [∗list] id ∈ kvVoters, nodeBoot γ kvRaftN kvVoters [] id)) =
      iprop(joinAuth γ (GMap.listToSet kvVoters) ∗
        [∗list] id ∈ kvVoters, nodeFounder (GF := GF) γ kvRaftN kvVoters id) := if_pos rfl
  rw [Hif]
  icases Hrest with ⟨-, Hfounders⟩
  imod confPolicy_alloc γ kvConfN kvRule E $$ Hdec with #Hpol
  imod rkvInv_alloc (GF := GF) E γ S0 $$ Hops HU with ⟨%γr, %Hγr, #Hinv, Hval, Hseqs⟩
  subst Hγr
  imod kvSnapInv_alloc γr E $$ Hsm with #Hsinv
  imodintro
  iexists γr
  isplitr
  · ipureintro; exact Hγ.1
  iframe Hinv Hval Hseqs Hfounders
  unfold kvCluster
  iframe Hiscl Hpol Hca0 Hsinv

end alloc

end EtcdGrove
end Perennial
