/-
Lean-first (no Rocq counterpart).

# Allocating the store's ghost state (2026-10-30, kvreconf-final, helper LIFE)

What `StartCluster` allocates besides raft's cluster (kv's `Alloc.lean`, changed where kvreconf
differs):

* `rkvInv_alloc`: the store's invariant over raft's cluster, from what `cluster_alloc` hands the
  client (no committed requested entry, no read context used), with every possible replica id's
  read sequence at `0` (`allIds`, the ids `1 … 9`: `maxReplicas`), the next operation id at `0`;
  the next-id bound and the stopper's flag are the caller's names (`γn`, `γs`). It gives the
  client's half of the store's state (`kvEmpty`), the lock's half of `γr.opn`, and the read
  sequence elements.
* `kvrSnapInv_alloc`: the registry of the snapshots made, from raft's `ownSnapsMade γ []`.
* `isStats_alloc`: a zero `Stats`'s counters, each in its invariant.
* `allIds_split`: the ids `1 … 9` are the founders `bootVoters k` and the fresh ids above them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClusterLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.LifeLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- Every replica id a cluster may start: `1 … 9`. -/
abbrev allIds : List w64 := bootVoters 9

/-- The map of the keys `l`, each to `v`. -/
def lifeConstMap {V : Type} (l : List w64) (v : V) : GMap w64 V :=
  match l with
  | [] => ∅
  | k :: l => GMap.insert k v (lifeConstMap l v)

theorem lifeConstMap_lookup {V : Type} (l : List w64) (v : V) (k : w64) :
    lifeConstMap l v !! k = if k ∈ l then some v else none := by
  induction l with
  | nil => rfl
  | cons k' l IH =>
    show (GMap.insert k' v (lifeConstMap l v)) !! k = _
    by_cases h : k' = k
    · subst h; rw [GMap.lookup_insert_eq]; simp
    · rw [GMap.lookup_insert_ne _ _ h, IH]; simp [List.mem_cons, Ne.symm h]

theorem allIds_split (k : Nat) (hk : k ≤ 9) : bootVoters k ++ freshIds (k + 1) = allIds := by
  induction h : 9 - k generalizing k with
  | zero =>
    have : k = 9 := by omega
    subst this
    have : freshIds 10 = [] := by decide
    rw [this, List.append_nil]
  | succ n IH =>
    have IH' := IH (k + 1) (by omega) (by omega)
    rw [← IH', freshIds_cons (k + 1) (by omega)]
    have : bootVoters (k + 1) = bootVoters k ++ [W64 ((k : Int) + 1)] := by
      simp [bootVoters, List.range_succ]
    rw [this, List.append_assoc]
    congr 3

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [StorageModel GF] [AllG GF]

/-- **The store's invariant** over raft's cluster `γ` (see the file header). -/
theorem rkvInv_alloc (E : CoPset) (γ : Cluster) (γn γs : GName) :
    ⊢ ownCommittedOps (GF := GF) γ [] -∗ ownReadCtxs γ ∅ ={E}=∗
      ∃ γr : RNames, ⌜γr.cluster = γ ∧ γr.nid = γn ∧ γr.stp = γs⌝ ∗ rkvInv γr ∗
        rkvVal γr kvEmpty ∗ ghostVar γr.opn (1 : Qp).half (W64 0) ∗
        [∗list] id ∈ allIds, id ↪[γr.rseq] W64 0 := by
  iintro Hops HU
  imod ghostVar_alloc (GF := GF) ([] : List (List w8)) with ⟨%γv, Hv⟩
  icases (ghostVar_split_half (GF := GF) γv 1 ([] : List (List w8))).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod ghostVar_alloc (GF := GF) (W64 0) with ⟨%γo, Ho⟩
  icases (ghostVar_split_half (GF := GF) γo 1 (W64 0)).1 $$ Ho with ⟨Ho1, Ho2⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := List w8) with ⟨%γmi, HMi⟩
  imod ghost_map_alloc (GF := GF) (lifeConstMap allIds (W64 0)) with ⟨%γrs, HRS, Hels⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64 × w64) (V := List w8) with ⟨%γrm, HRM⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := GName × GName) with ⟨%γop, HO⟩
  imod ghost_map_alloc_empty (GF := GF) (K := GName) (V := ReadRec) with ⟨%γrd, HRD⟩
  let γr : RNames := ⟨γ, γv, γo, γmi, γrs, γrm, γop, γn, γs, γrd⟩
  imod inv_alloc rkvN E (rkvInvBody (GF := GF) γr) $$ [Hops Hv1 HU Ho1 HMi HRS HRM HO HRD]
    with #Hinv
  · inext
    unfold rkvInvBody
    iexists [], W64 0, ∅, lifeConstMap allIds (W64 0), ∅, ∅, ∅
    isplitl [Hops Hv1 HU Ho1 HMi HRS HRM HO]
    · unfold kvCore
      simp only [show logHist ([] : List LogEntry) = [] from rfl]
      iframe Hops Hv1 HU Ho1 HMi HRS HRM HO
      ipureintro
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · intro i d h; simp at h
      · intro r s c h; simp at h
      · intro d γp h; simp at h
      · intro c h; rw [GMap.elem_of_gset] at h; simp at h
      · intro d h; simp at h
      · intro e h; simp at h
    · unfold rkvSlots readReg
      isplitl []
      · iapply BigSepM.bigSepM_empty.2
        itrivial
      iexists ∅
      iframe HRD
      iapply BigSepM.bigSepM_empty.2
      itrivial
  imodintro
  iexists γr
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  unfold rkvInv rkvVal
  iframe Hinv Ho2
  isplitl [Hv2]
  · iexists []
    iframe Hv2
    ipureintro; rfl
  ihave Hl := bigSepM_keys (fun k x => iprop(k ↪[γrs] x)) allIds (lifeConstMap allIds (W64 0))
    (bootVoters_nodup 9 (by omega)) (fun k => by rw [lifeConstMap_lookup]; split <;> simp_all)
    $$ Hels
  iapply (BigSepL.bigSepL_mono (Φ := fun _ k => iprop(∃ x, ⌜lifeConstMap allIds (W64 0) !! k = some x⌝ ∗
    k ↪[γrs] x)) ?_) $$ Hl
  intro j k hj
  iintro ⟨%x, %hx, H⟩
  rw [lifeConstMap_lookup, ite_eq_left (List.mem_of_getElem? hj)] at hx
  cases hx
  iexact H

/-- **The registry of the snapshots made**, none yet. -/
theorem kvrSnapInv_alloc (γr : RNames) (E : CoPset) :
    ⊢ ownSnapsMade (GF := GF) γr.cluster [] ={E}=∗ kvrSnapInv γr := by
  iintro H
  unfold kvrSnapInv
  iapply inv_alloc
  inext
  iexists []
  iframe H
  iapply (BigSepL.bigSepL_nil).2; iempintro

/-- A zero counter, in its invariant. -/
theorem counter_alloc (l : Loc) (E : CoPset) :
    ⊢ (l ↦ (zero_val sync.atomic.Uint64) : IProp GF) ={E}=∗ isCounter l := by
  have hz : (l ↦ (zero_val sync.atomic.Uint64) : IProp GF) ⊢
      sync.atomic.ownUint64 l (DFrac.own 1) (W64 0) := by
    rw [sync.atomic.ownUint64_unseal]; unfold sync.atomic.ownUint64Def; exact .rfl
  iintro H
  unfold isCounter
  iapply inv_alloc
  inext
  iexists W64 0
  iapply hz $$ H

/-- **A zero `Stats`**, its counters each in its invariant. -/
theorem isStats_alloc (st : Loc) (E : CoPset) :
    ⊢ (st ↦ (zero_val RStats) : IProp GF) ={E}=∗ isStats st := by
  iintro H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  icases H with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, -⟩
  imod counter_alloc _ E $$ H1 with #H1
  imod counter_alloc _ E $$ H2 with #H2
  imod counter_alloc _ E $$ H3 with #H3
  imod counter_alloc _ E $$ H4 with #H4
  imod counter_alloc _ E $$ H5 with #H5
  imod counter_alloc _ E $$ H6 with #H6
  imod counter_alloc _ E $$ H7 with #H7
  imod counter_alloc _ E $$ H8 with #H8
  imod counter_alloc _ E $$ H9 with #H9
  imod counter_alloc _ E $$ H10 with #H10
  imod counter_alloc _ E $$ H11 with #H11
  imod counter_alloc _ E $$ H12 with #H12
  imod counter_alloc _ E $$ H13 with #H13
  imod counter_alloc _ E $$ H14 with #H14
  imod counter_alloc _ E $$ H15 with #H15
  imod counter_alloc _ E $$ H16 with #H16
  imodintro
  unfold isStats
  simp only [statsFields]
  iframe #
  iapply (BigSepL.bigSepL_nil).2; iempintro

end alloc

end kvreconf
end EtcdGrove
end Perennial
