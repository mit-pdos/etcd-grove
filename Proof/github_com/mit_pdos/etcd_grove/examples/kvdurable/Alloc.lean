/-
Lean-first (no Rocq counterpart).

# Allocating the durable store's ghost state (2026-11-01, kvdurable's adequacy)

What `StartCluster.spec` takes allocated, and the client's half of the store's state, from raft's
`cluster_alloc` (no bootstrap log, `dup = true`) and the files the program owns (kvreconf's
`Alloc.lean`, whose `StartCluster` allocated it all in its proof; kvdurable's `StartCluster` takes it
from its caller, `Run`):

* `kdRkvInv_alloc`: the store's invariant (kvreconf's `rkvInv_alloc`, at kvdurable's names), with
  the read sequence of every id `0 … 9` at `0` (`freshIds 0`, what `StartCluster` takes);
* `kdSnapInv_alloc`: the registry of the snapshots made, none yet;
* `kdWr_alloc`: a writer variable per id;
* `kd_alloc`: all of it: `kdCluster`, the voters' durable states, vacant slots, files and writer
  variables, the join authority, the fresh ids' files and writer variables, the lock's halves and
  authorities, the empty map of the current incarnations, the crasher's token, and the client's
  `rkvVal γ kvEmpty`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Alloc

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- **The store's invariant** over raft's cluster `γc` (kvreconf's `rkvInv_alloc`): the other names
are the caller's. -/
theorem kdRkvInv_alloc (E : CoPset) (γc : Cluster) (γn γs files cur crt : GName)
    (wr : w64 → GName) :
    ⊢ ownCommittedOps (GF := GF) γc [] -∗ ownReadCtxs γc ∅ ={E}=∗
      ∃ γ : KdNames, ⌜γ.r.cluster = γc ∧ γ.r.nid = γn ∧ γ.files = files ∧ γ.wr = wr ∧
          γ.cur = cur ∧ γ.crt = crt⌝ ∗ rkvInv γ ∗
        rkvVal γ kvreconf.kvEmpty ∗ ghostVar γ.r.opn (1 : Qp).half (W64 0) ∗
        [∗list] id ∈ kvreconf.freshIds 0, id ↪[γ.r.rseq] W64 0 := by
  iintro Hops HU
  imod ghostVar_alloc (GF := GF) ([] : List (List w8)) with ⟨%γv, Hv⟩
  icases (ghostVar_split_half (GF := GF) γv 1 ([] : List (List w8))).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod ghostVar_alloc (GF := GF) (W64 0) with ⟨%γo, Ho⟩
  icases (ghostVar_split_half (GF := GF) γo 1 (W64 0)).1 $$ Ho with ⟨Ho1, Ho2⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := List w8) with ⟨%γmi, HMi⟩
  imod ghost_map_alloc (GF := GF) (kvreconf.lifeConstMap (kvreconf.freshIds 0) (W64 0))
    with ⟨%γrs, HRS, Hels⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64 × w64) (V := List w8) with ⟨%γrm, HRM⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := GName × GName) with ⟨%γop, HO⟩
  imod ghost_map_alloc_empty (GF := GF) (K := GName) (V := kvreconf.ReadRec) with ⟨%γrd, HRD⟩
  let γ : KdNames := ⟨⟨γc, γv, γo, γmi, γrs, γrm, γop, γn, γs, γrd⟩, files, wr, cur, crt⟩
  imod inv_alloc kdRkvN E (rkvInvBody (GF := GF) γ) $$ [Hops Hv1 HU Ho1 HMi HRS HRM HO HRD]
    with #Hinv
  · inext
    unfold rkvInvBody
    iexists [], W64 0, ∅, kvreconf.lifeConstMap (kvreconf.freshIds 0) (W64 0), ∅, ∅, ∅
    isplitl [Hops Hv1 HU Ho1 HMi HRS HRM HO]
    · unfold kvCore
      simp only [show kvreconf.logHist ([] : List LogEntry) = [] from rfl]
      iframe Hops Hv1 HU Ho1 HMi HRS HRM HO
      ipureintro
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · intro i d h; simp at h
      · intro r s c h; simp at h
      · intro d γp h; simp at h
      · intro c h; rw [GMap.elem_of_gset] at h; simp at h
      · intro d h; simp at h
      · intro e h; simp at h
    · isplitl []
      · iapply BigSepM.bigSepM_empty.2
        itrivial
      unfold readReg
      iexists ∅
      iframe HRD
      iapply BigSepM.bigSepM_empty.2
      itrivial
  imodintro
  iexists γ
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold rkvInv rkvVal
  iframe Hinv Ho2
  isplitl [Hv2]
  · iexists []
    iframe Hv2
    ipureintro; rfl
  have Hnd : (kvreconf.freshIds 0).Nodup := by decide
  ihave Hl := kvreconf.bigSepM_keys (fun k x => iprop(k ↪[γrs] x)) (kvreconf.freshIds 0)
    (kvreconf.lifeConstMap (kvreconf.freshIds 0) (W64 0)) Hnd
    (fun k => by rw [kvreconf.lifeConstMap_lookup]; split <;> simp_all) $$ Hels
  iapply (BigSepL.bigSepL_mono (Φ := fun _ k => iprop(∃ x,
    ⌜kvreconf.lifeConstMap (kvreconf.freshIds 0) (W64 0) !! k = some x⌝ ∗ k ↪[γrs] x)) ?_) $$ Hl
  intro j k hj
  iintro ⟨%x, %hx, H⟩
  rw [kvreconf.lifeConstMap_lookup, ite_eq_left (List.mem_of_getElem? hj)] at hx
  cases hx
  iexact H

/-- **The registry of the snapshots made**, none yet. -/
theorem kdSnapInv_alloc (γ : KdNames) (E : CoPset) :
    ⊢ ownSnapsMade (GF := GF) γ.r.cluster [] ={E}=∗ kdSnapInv γ := by
  iintro H
  unfold kdSnapInv
  iapply inv_alloc
  inext
  iexists []
  iframe H
  iapply (BigSepL.bigSepL_nil).2; iempintro

/-- **A writer variable per id** of `ids` (distinct), each at `g0`. -/
theorem kdWr_alloc (g0 : RaftState × Option GoString) : ∀ ids : List w64, ids.Nodup →
    ⊢ |==> ∃ wr : w64 → GName, [∗list] i ∈ ids, ghostVar (GF := GF) (wr i) (1 : Qp) g0
  | [], _ => by
    iintro
    imodintro
    iexists (fun _ => 0)
    iapply (BigSepL.bigSepL_nil).2; iempintro
  | i :: ids, Hnd => by
    have Hnd' := List.nodup_cons.1 Hnd
    iintro
    imod kdWr_alloc g0 ids Hnd'.2 with ⟨%wr, Hs⟩
    imod ghostVar_alloc (GF := GF) g0 with ⟨%γi, Hi⟩
    imodintro
    iexists (fun j => if j = i then γi else wr j)
    iapply BigSepL.bigSepL_cons.2
    simp only [↓reduceIte]
    iframe Hi
    iapply (BigSepL.bigSepL_mono (Φ := fun _ j => ghostVar (GF := GF) (wr j) (1 : Qp) g0) ?_) $$ Hs
    intro k j hj
    have hne : j ≠ i := fun h => Hnd'.1 (h ▸ List.mem_of_getElem? hj)
    simp only [hne, ↓reduceIte]
    exact .rfl

/-- The voters' files and writer variables, and the fresh ids', from every id's. -/
theorem kd_split_ids (k : Nat) (hk : k ≤ 9) (Φ : w64 → IProp GF) :
    ([∗list] i ∈ kvreconf.allIds, Φ i) ⊢
      ([∗list] i ∈ kvreconf.bootVoters k, Φ i) ∗ [∗list] i ∈ kvreconf.freshIds (k + 1), Φ i := by
  rw [← kvreconf.allIds_split k hk]
  exact (BigSepL.bigSepL_append).1

/-- **Everything `StartCluster` takes allocated** (see the file header), for options a cluster may
run with, from the files' invariant and every id's file, absent. -/
theorem kd_alloc (o : KOptions) (dir : GoString) (γf : GName) (E : CoPset)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Ho : kdOptsOk o) :
    ⊢ durableFilesInv (GF := GF) γf kdFilesN -∗
      ([∗list] i ∈ kvreconf.allIds, dfile γf (kdFileName dir i) none) ={E}=∗
      ∃ γ : KdNames,
        ⌜γ.files = γf ∧ γ.r.cluster.dup = true ∧ γ.r.cluster.bootLen = 0⌝ ∗ kdCluster γ (kvreconf.bootVoters (uint.nat o.Voters')) ∗
        ([∗list] id ∈ kvreconf.bootVoters (uint.nat o.Voters'), raftState γ.r.cluster id RaftState.init ∗ nodeVacant γ.r.cluster id ∗
          dfile γ.files (kdFileName dir id) none ∗
          ∃ g : RaftState × Option GoString, ghostVar (γ.wr id) (1 : Qp) g) ∗
        joinAuth γ.r.cluster (GMap.listToSet (kvreconf.bootVoters (uint.nat o.Voters'))) ∗
        ([∗list] i ∈ kvreconf.freshIds ((kvreconf.bootVoters (uint.nat o.Voters')).length + 1), dfile γ.files (kdFileName dir i) none ∗
          ∃ g : RaftState × Option GoString, ghostVar (γ.wr i) (1 : Qp) g) ∗
        ghostVar γ.r.opn (1 : Qp).half (W64 0) ∗ monoNatAuthOwn γ.r.nid 1 0 ∗
        ([∗list] i ∈ kvreconf.freshIds 0, i ↪[γ.r.rseq] W64 0) ∗
        ghostMapAuth γ.cur 1 (∅ : GMap w64 Loc) ∗ crasher γ ∗ rkvVal γ kvreconf.kvEmpty := by
  obtain ⟨Hv1, Hv5, -⟩ := Ho
  have Hk9 : uint.nat o.Voters' ≤ 9 := by word
  have Hlen := kvreconf.bootVoters_length (uint.nat o.Voters')
  iintro #Hfiles Hfs
  -- raft's cluster, with no bootstrap log
  imod cluster_alloc (GF := GF) kdRaftN (kvreconf.bootVoters (uint.nat o.Voters')) [] [] true E
    Hrb (by intro h; rw [h] at Hlen; simp at Hlen; word)
    (kvreconf.bootVoters_nodup _ (by omega)) (kvreconf.bootVoters_zero _ (by omega))
    (by rw [Hlen]; word) (fun h => absurd rfl h) $$ [] with
    ⟨%γc, %Hd, Hops, HU, #Hcl, Hdec, #Hca, Hsm, Hrs, Hja⟩
  · simp only [↓reduceIte]; iempintro
  simp only [↓reduceIte] at Hd ⊢
  imod confPolicy_alloc γc kdConfN kvreconf.kvrRule E $$ Hdec with #Hpol
  -- the other names
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γn, Hn, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Loc) with ⟨%γcur, Hcur⟩
  imod token_alloc (GF := GF) with ⟨%γcrt, Hcrt⟩
  imod kdWr_alloc (GF := GF) (RaftState.init, none) kvreconf.allIds
    (kvreconf.bootVoters_nodup 9 (by omega)) with ⟨%wr, Hwr⟩
  imod kdRkvInv_alloc E γc γn 0 γf γcur γcrt wr $$ Hops HU with
    ⟨%γ, %Hγ, Hinv, Hval, Hopn, Hrseq⟩
  obtain ⟨Hγc, Hγn, Hγf, Hγwr, Hγcur, Hγcrt⟩ := Hγ
  imod kdSnapInv_alloc γ E $$ [Hsm] with Hsnap
  · rw [Hγc]; iexact Hsm
  imodintro
  iexists γ
  rw [Hγc, Hγn, Hγf, Hγwr, Hγcur]
  icases kd_split_ids (uint.nat o.Voters') Hk9 _ $$ Hfs with ⟨HfV, HfF⟩
  icases kd_split_ids (uint.nat o.Voters') Hk9 _ $$ Hwr with ⟨HwV, HwF⟩
  rw [Hlen]
  iframe Hja Hopn Hn Hrseq Hcur Hval
  isplitr
  · ipureintro; exact ⟨rfl, Hd.1, Hd.2⟩
  isplitl [Hsnap Hinv]
  · unfold kdCluster
    rw [Hγc, Hγf]
    iframe Hcl Hpol Hca Hsnap Hinv Hfiles
  isplitl [Hrs HfV HwV]
  · ihave HV := (BigSepL.bigSepL_sep_eqv (Φ := fun _ id => iprop(raftState (GF := GF) γc id
      RaftState.init ∗ nodeVacant γc id)) (Ψ := fun _ id => iprop(dfile γf (kdFileName dir id) none ∗
      ghostVar (wr id) (1 : Qp) (RaftState.init, (none : Option GoString))))
      (l := kvreconf.bootVoters (uint.nat o.Voters'))).2 $$ [Hrs HfV HwV]
    · iframe Hrs
      iapply (BigSepL.bigSepL_sep_eqv (Φ := fun _ id => dfile (GF := GF) γf (kdFileName dir id) none)
        (Ψ := fun _ id => ghostVar (GF := GF) (wr id) (1 : Qp) (RaftState.init, (none : Option GoString)))
        (l := kvreconf.bootVoters (uint.nat o.Voters'))).2
      iframe HfV HwV
    iapply (BigSepL.bigSepL_mono ?_) $$ HV
    intro k id hk
    iintro ⟨⟨Hr, Hv⟩, Hf, Hw⟩
    iframe Hr Hv Hf
    iexists _
    iexact Hw
  isplitl [HfF HwF]
  · ihave HF := (BigSepL.bigSepL_sep_eqv (Φ := fun _ id => dfile (GF := GF) γf (kdFileName dir id) none)
        (Ψ := fun _ id => ghostVar (GF := GF) (wr id) (1 : Qp) (RaftState.init, (none : Option GoString)))
        (l := kvreconf.freshIds (uint.nat o.Voters' + 1))).2 $$ [HfF HwF]
    · iframe HfF HwF
    iapply (BigSepL.bigSepL_mono ?_) $$ HF
    intro k id hk
    iintro ⟨Hf, Hw⟩
    iframe Hf
    iexists _
    iexact Hw
  unfold crasher
  rw [Hγcrt]
  iexact Hcrt

end alloc

end kvdurable
end EtcdGrove
end Perennial
