/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__NoConflictAppendEntriesRequest`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__NoConflictAppendEntriesRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__HasNoConflict
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.SubSeq

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

-- Not enabled: `nil` (hygiene off).
set_option hygiene false in
local macro "cf_none" pf:term : tactic => `(tactic| (
    try wp_auto
    imodintro
    iapply HΦ
    have : st.noConflictAppendEntriesRequest (uint.nat i) (sint.Z index) m = .ok none := $pf
    rw [this]
    ipureintro; rfl))

theorem State.NoConflictAppendEntriesRequest.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_mut : State.mut.spec (GF := GF) (hG := hG))
    (wp_HasNoConflict : State.HasNoConflict.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG)) :
    State.NoConflictAppendEntriesRequest.spec (GF := GF) (hG := hG) := by
  intro p st i index q m
  wp_start as ⟨#Hst, #Hmsg, %Hi, %hx1, %hx2, %hp1, %hp2, %hll, %hel⟩
  read_server
  read_msg
  iunfold logRO at Hve
  icases Hve with ⟨%fs, #Hfs, #Hfl⟩
  ihave %Hfsl := ownSlice_len $$ Hfs
  ihave %Hfll := BigSepL2.bigSepL2_length $$ Hfl
  iapply wp_fupd
  wp_auto
  lookup_server
  have hlen : sint.Z gs.Log'.len = ((st.s (uint.nat i)).log.length : Int) := by rw [← Hell, Hesl.1]; word
  have hflen : sint.Z gm.Entries'.len = (m.entries.length : Int) := by rw [← Hfll, Hfsl.1]; word
  have hz := uint_eq_iff gm.Entries'.len (W64 0) _ 0 (by rw [show uint.nat gm.Entries'.len = m.entries.length by have := hflen; word]) rfl
  by_cases hB1 : m.entries.length = 0
  · rw [decide_eq_true (hz.2 hB1)]
    have hne : m.entries = [] := List.eq_nil_of_length_eq_zero hB1
    cf_none (by unfold State.noConflictAppendEntriesRequest; simp [hne]; rfl)
  rw [decide_eq_false (fun e => hB1 (hz.1 e))]
  have hne : m.entries ≠ [] := fun h => hB1 (by simp [h])
  wp_auto
  have hci : sint.Z gs.CommitIndex' < sint.Z index ↔ (st.s (uint.nat i)).commitIndex < sint.Z index := by
    rw [Hf.2.2.2.2.1]
  by_cases hA : (st.s (uint.nat i)).commitIndex < sint.Z index
  rotate_left
  · rw [decide_eq_false (fun e => hA (hci.1 e))]
    cf_none (by unfold State.noConflictAppendEntriesRequest; simp [hne, hA]; rfl)
  rw [decide_eq_true (hci.2 hA)]
  wp_auto
  wp_apply wp_HasNoConflict p st i index gm.Entries' m.entries $$ [Hst]
  · iframe Hst
    isplitl []
    · iunfold logRO; iexists fs; iframe Hfs Hfl
    ipureintro; exact ⟨Hi, hx1, hx2, hll, hel⟩
  cases hnc : st.hasNoConflict (uint.nat i) (sint.Z index) m.entries
  · cf_none (by unfold State.noConflictAppendEntriesRequest; simp [hne, hA, hnc]; rfl)
  wp_auto
  have hpn : sint.Z (gm.PrevLogIndex' + gm.Entries'.len) = m.prevLogIndex + m.entries.length := by
    have := Hv.2.2.2.2.2.2.1; rw [← hflen, ← this]; word
  have hgtc : sint.Z gs.Log'.len < sint.Z (gm.PrevLogIndex' + gm.Entries'.len) ↔
      ((st.s (uint.nat i)).log.length : Int) < m.prevLogIndex + m.entries.length := by rw [hpn, hlen]
  by_cases hgt : ((st.s (uint.nat i)).log.length : Int) < m.prevLogIndex + m.entries.length
  rotate_left
  · rw [decide_eq_false (fun e => hgt (hgtc.1 e))]
    cf_none (by unfold State.noConflictAppendEntriesRequest; simp [hne, hA, hnc, hgt]; rfl)
  rw [decide_eq_true (hgtc.2 hgt)]
  wp_auto
  have hix : sint.Z index ≤ ((st.s (uint.nat i)).log.length : Int) + 1 := by
    unfold State.hasNoConflict at hnc; simp at hnc; exact hnc.1
  cases hs : subSeq m.entries (((st.s (uint.nat i)).log.length : Int) - sint.Z index + 2) (m.entries.length : Int) with
  | none =>
    exfalso; unfold subSeq at hs; split at hs
    · cases hs
    · split at hs
      · omega
      · cases hs
  | some r =>
  wp_apply wp_clone p st $$ [Hst] as %t Ht
  · iexact Hst
  try wp_auto
  mut_open t, st, [], i, Ht
  try wp_auto
  wp_apply wp_SubSeq gm.Entries' m.entries _ _ r $$ [] as %u #Hu
  · isplitl []
    · iunfold logRO; iexists fs; iframe Hfs Hfl
    ipureintro
    rw [show sint.Z (gs.Log'.len - index + W64 2) = (((st.s (uint.nat i)).log.length : Int) - sint.Z index + 2) by rw [← hlen]; word, hflen]
    exact hs
  try wp_auto
  ihave %Hesw := ownSlice_wf $$ Hes
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; exact Hesw.1, Int.le_refl _, Hesw.2⟩)]
  ihave #Hfsl := ownSlice_fullSlice_len _ _ _ $$ Hes
  ihave Hfcap := ownSliceCap_empty (V := G.Entry) (GF := GF)
    (slice.fullSlice gs.Log' G.Entry (W64 0) gs.Log'.len gs.Log'.len) (by simp [slice.fullSlice])
    (by simp only [slice.fullSlice]; rw [show gs.Log'.len - W64 0 = gs.Log'.len by word]; exact Hesw.1)
  iunfold logRO at Hu
  icases Hu with ⟨%us, #Hus, #Hul⟩
  wp_auto
  wp_apply wp_slice_append_persistent _ es _ us DfracDiscarded $$ [Hfsl Hfcap Hus] as %s2 ⟨#Hs2, -, -⟩
  · iframe Hus
    isplitr
    · iexact Hfsl
    iexact Hfcap
  try wp_auto
  ihave #Hnl : logRO (GF := GF) s2 ((st.s (uint.nat i)).log ++ r) $$ []
  · iunfold logRO
    iexists _
    iframe Hs2
    iapply (BigSepL2.bigSepL2_append (Or.inl Hell)).2
    iframe Hel Hul
  close_copy' { gc with Log' := s2 }, (fun (v : Server) => { v with log := (st.s (uint.nat i)).log ++ r }), Hcf with Hnl Hcr Hcg Hcc Hcd
  imodintro
  iapply HΦ
  have : st.noConflictAppendEntriesRequest (uint.nat i) (sint.Z index) m = .ok (some (st.upd (uint.nat i) (fun (v : Server) => { v with log := (st.s (uint.nat i)).log ++ r }))) := by
    unfold State.noConflictAppendEntriesRequest subSeqM; simp [hne, hA, hnc, hgt, hs]; rfl
  rw [this]
  dsimp only
  iexists _; iexact Hs

end proof

end Etcdraft
end EtcdGrove
end Perennial
