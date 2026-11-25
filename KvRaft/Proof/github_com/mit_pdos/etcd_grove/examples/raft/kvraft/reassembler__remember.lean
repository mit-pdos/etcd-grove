/-
The proof of `KvRaft/Spec/.../kvraft/reassembler__remember.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.reassembler__remember
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Stats__add

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

/-- A map of owned slices, at one key: the slice there (nil if none), and the map back with any
slice at that key. -/
private theorem bigSepM_slice_acc (Ψ : w64 → GoSlice → IProp GF) (M : GMap w64 GoSlice) (k : w64)
    (h0 : ⊢ Ψ k (zero_val GoSlice)) :
    ([∗map] k ↦ v ∈ M, Ψ k v) ⊢
      Ψ k ((M !! k).getD (zero_val GoSlice)) ∗ ∀ x, Ψ k x -∗ [∗map] k ↦ v ∈ <[k := x]> M, Ψ k v := by
  iintro HM
  cases h : M !! k with
  | none =>
    simp only [Option.getD_none]
    isplitl []
    · iapply h0
    iintro %x Hx
    iapply (BigSepM.bigSepM_insert h).2
    iframe Hx HM
  | some v =>
    simp only [Option.getD_some]
    icases (BigSepM.bigSepM_delete h).1 $$ HM with ⟨Hv, HM⟩
    iframe Hv
    iintro %x Hx
    iapply BigSepM.bigSepM_insert_delete.2
    iframe Hx HM

theorem reassembler.remember.wp_proof
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    reassembler.remember.spec (GF := GF) (hG := hG) := by
  intro F γu r src mid snap
  wp_start as Hr
  iunfold ownReassembler at Hr
  icases Hr with ⟨%pm, %dm, %lm, %sts, %P, %D, %Ls, #Hpm, #Hdm, #Hlm, #Hsts, #Hs, HP, HD, HLs, HPs, HDs⟩
  try wp_auto
  wp_apply (wp_map_lookup1 (K := w64) (V := GoSlice) go.uint64 _ dm D src (DFrac.own 1)) $$ HD as HD
  icases bigSepM_slice_acc _ D src ?_ $$ HDs with ⟨⟨%ds, Hds, Hdsc⟩, HDs⟩
  · iexists []
    isplitl
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  generalize (D !! src).getD (zero_val GoSlice) = dsl
  try wp_auto
  ihave %Hdsl := ownSlice_len $$ Hds
  ihave %Hdsw := ownSlice_wf $$ Hds
  wp_if_destruct
  -- the oldest completed name forgotten (the if's first goal)
  rw [ite_eq_left (by refine ⟨by decide, by word, by word⟩)]
  icases (ownSlice_split_all (W64 1) dsl (DFrac.own 1) ds ⟨by decide, by word⟩).1 $$ Hds with ⟨-, Hds1⟩
  ihave Hn := ownSlice_nil (V := github_com.mit_pdos.etcd_grove.examples.raft.kvraft.doneMsg) (GF := GF) (DFrac.own 1)
  ihave Hnc := ownSliceCap_nil (V := github_com.mit_pdos.etcd_grove.examples.raft.kvraft.doneMsg) (GF := GF)
  try wp_auto
  wp_apply (wp_slice_append (V := github_com.mit_pdos.etcd_grove.examples.raft.kvraft.doneMsg)
    slice.nil [] _ (List.drop (sint.nat (W64 1)) ds) (DFrac.own 1)) $$ [$Hn $Hnc $Hds1]
    as %dsl2 ⟨Hds, Hdsc, -⟩
  all_goals try wp_auto
  -- the name remembered
  all_goals
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sl1 ⟨Hsl1, -⟩
    try wp_auto
    wp_apply wp_slice_append $$ [$Hds $Hdsc $Hsl1] as %dsl3 ⟨Hds, Hdsc, -⟩
    try wp_auto
    wp_apply (wp_mapInsert (K := w64) (V := GoSlice) go.uint64 dm D src dsl3) $$ HD as HD
    ihave HDs := HDs $$ %dsl3 [Hds Hdsc]
    · iexists _; iframe Hds Hdsc
    try wp_auto
    wp_apply (wp_map_lookup1 (K := w64) (V := GoSlice) go.uint64 _ pm P src (DFrac.own 1)) $$ HP as HP
    icases bigSepM_slice_acc _ P src ?_ $$ HPs with ⟨⟨%ps, Hps, Hpsc, Hown⟩, HPs⟩
    · iexists []
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      iapply BigSepL.bigSepL_nil.2; iempintro
    generalize (P !! src).getD (zero_val GoSlice) = psl
    try wp_auto
    ihave %Hpsl := ownSlice_len $$ Hps
    irename : from_ptr ↦ src => Hfromv
    ihave IH : iprop(∃ (k : w64) (pv : Loc) (kv : GoSlice) (kept : List Loc),
        "i" ∷ i_ptr ↦ k ∗ "p" ∷ p_ptr ↦ pv ∗ "keep" ∷ keep_ptr ↦ kv ∗
        "Hkeep" ∷ kv ↦* kept ∗ "Hkc" ∷ ownSliceCap Loc kv (DFrac.own 1) ∗
        "Hkept" ∷ ([∗list] q ∈ kept, ownPartial F γu src q) ∗
        "Hps" ∷ psl ↦* ps ∗
        "Hrest" ∷ ([∗list] q ∈ ps.drop (sint.nat k), ownPartial F γu src q) ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ps.length : Int)⌝) $$ [i p keep Hps Hown]
    · iexists W64 0, _, _, []
      iframe i p keep Hps
      isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      isplitl []
      · iapply BigSepL.bigSepL_nil.2; iempintro
      simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
      iframe Hown
      ipureintro; exact ⟨by decide, by word⟩
    wp_for IH
    wp_if_destruct
    · have Hif' : sint.Z k < sint.Z psl.len := Hif
      have Hlt : sint.nat k < ps.length := by rw [Hpsl.1]; word
      obtain ⟨q, Hq⟩ : ∃ q, ps[sint.nat k]? = some q := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z psl.len := ⟨Hk.1, Hif'⟩
      simp only [Hbnd', _root_.and_self]
      wp_apply wp_load_slice_index psl (sint.Z k) _ (DFrac.own 1) q Hk.1 $$ [Hps] as Hps
      · iframe Hps; ipureintro; exact Hq
      have Hdrop : ps.drop (sint.nat k) = q :: ps.drop (sint.nat k + 1) := by
        rw [List.drop_eq_getElem_cons Hlt]
        rw [List.getElem?_eq_getElem Hlt] at Hq
        rw [Option.some.inj Hq]
      rw [Hdrop]
      icases Hrest with ⟨Hq, Hrest⟩
      iunfold ownPartial at Hq
      icases Hq with ⟨%qid, %cs, %chs, %hv, %tp, %got, Hqid, Hqcs, Hqhv, Hqtp, Hqchs, %Hgot, Hqslots⟩
      try wp_auto
      have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      wp_if_destruct
      all_goals try wp_if_destruct
      all_goals try wp_if_destruct
      all_goals try wp_if_destruct
      all_goals try wp_auto
      all_goals
        ihave Hq : ownPartial F γu src q $$ [Hqid Hqcs Hqhv Hqtp Hqchs Hqslots]
        · iunfold ownPartial
          iexists qid, cs, chs, hv, tp, got
          iframe
          ipureintro; exact Hgot
      all_goals first
        | (-- evicted (stale)
           wp_apply wp_add sts (W64 30) (by decide) (by decide) $$ [$Hpkg $Hs]
           try wp_auto
           wp_for_post
           iframe
           iexists k + W64 1, q, kv, kept
           rw [Hk1]
           iframe
           ipureintro; exact ⟨by word, by word⟩)
        | (-- kept
           wp_apply wp_slice_literal
           try (isplitr; (ipureintro; rfl))
           iintro %sl1 ⟨Hsl1, -⟩
           try wp_auto
           wp_apply wp_slice_append $$ [$Hkeep $Hkc $Hsl1] as %kv' ⟨Hkeep, Hkc, -⟩
           wp_for_post
           iframe
           iexists k + W64 1, q, kv', kept ++ [q]
           rw [Hk1]
           iframe
           isplitl []
           · iapply BigSepL.bigSepL_nil.2; iempintro
           ipureintro; exact ⟨by word, by word⟩)
    · -- the messages in progress kept, the latest name updated
      try wp_auto
      wp_apply (wp_mapInsert (K := w64) (V := GoSlice) go.uint64 pm P src kv) $$ HP as HP
      ihave HPs := HPs $$ %kv [Hkeep Hkc Hkept]
      · iexists kept; iframe
      try wp_auto
      wp_apply (wp_map_lookup2 (K := w64)
        (V := github_com.mit_pdos.etcd_grove.examples.raft.kvraft.msgID) go.uint64 _ lm Ls src
        (DFrac.own 1)) $$ HLs as HLs
      try wp_auto
      all_goals try wp_if_destruct
      all_goals try wp_if_destruct
      all_goals try wp_if_destruct
      all_goals try wp_auto
      all_goals first
        | (wp_apply wp_add sts (W64 28) (by decide) (by decide) $$ [$Hpkg $Hs]
           try wp_auto
           iapply HΦ
           iunfold ownReassembler
           iexists pm, dm, lm, sts, _, _, _
           iframe Hpm Hdm Hlm Hsts Hs
           iframe; done)
        | (wp_apply (wp_mapInsert (K := w64)
             (V := github_com.mit_pdos.etcd_grove.examples.raft.kvraft.msgID) go.uint64 lm Ls src mid)
             $$ HLs as HLs
           try wp_auto
           iapply HΦ
           iunfold ownReassembler
           iexists pm, dm, lm, sts, _, _, _
           iframe Hpm Hdm Hlm Hsts Hs
           iframe; done)
end proof

end kvraft
end EtcdGrove
end Perennial
