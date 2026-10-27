/-
Lean-first (no Rocq counterpart).

# Allocating the store's ghost state (2026-10-10)

What a cluster's set-up gives the replicas' `NewStorage` and `New`:

* `kvStorInv_alloc`: the storage registry's invariant, from the authority of an empty
  ghost map at the registry's name (allocated first, `ghost_map_alloc_empty`, and made the
  `KVStor` instance).
* `rkvInv_alloc`: the store's invariant over raft's cluster, from what the cluster's allocation
  (`Draft.cluster_alloc_static`) hands the client -- the committed requested entries (none) and the
  read contexts (none used) -- with the client's half of the value (the empty store, `kvEmpty`)
  and the replicas' sequence-number tokens at `S0` (for `New`, each at 0).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas

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
    ⊢ ghostMapAuth (KVStor.kvStorName (GF := GF)) 1 (∅ : GMap Loc MemStorRec) ={E}=∗
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
(`Draft.cluster_alloc_static`): the committed requested entries, none, and the read contexts, none
used; with the client's half of the value and the sequence-number tokens of `S0` (`New` takes
`id ↪[γr.seq] 0`). -/
theorem rkvInv_alloc (E : CoPset) (γ : Draft.Cluster) (S0 : GMap w64 w64) :
    ⊢ Draft.ownCommittedOps (GF := GF) γ [] -∗ Draft.ownReadCtxs γ ∅ ={E}=∗
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
      simp only [show logHist ([] : List Draft.LogEntry) = [] from rfl]
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

end alloc

end EtcdGrove
end Perennial
