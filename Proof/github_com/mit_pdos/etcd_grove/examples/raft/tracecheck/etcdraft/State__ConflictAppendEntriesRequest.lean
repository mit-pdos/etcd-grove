/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__ConflictAppendEntriesRequest`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__ConflictAppendEntriesRequest
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
    have : st.conflictAppendEntriesRequest (uint.nat i) (sint.Z index) m = .ok none := $pf
    rw [this]
    ipureintro; rfl))

theorem State.ConflictAppendEntriesRequest.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_mut : State.mut.spec (GF := GF) (hG := hG))
    (wp_HasNoConflict : State.HasNoConflict.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG)) :
    State.ConflictAppendEntriesRequest.spec (GF := GF) (hG := hG) := by
  intro p st i index q m
  wp_start as ⟨#Hst, #Hmsg, %Hi, %hx1, %hx2, %hll, %hel⟩
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
    cf_none (by unfold State.conflictAppendEntriesRequest; simp [hne]; rfl)
  rw [decide_eq_false (fun e => hB1 (hz.1 e))]
  have hne : m.entries ≠ [] := fun h => hB1 (by simp [h])
  wp_auto
  have hci : sint.Z gs.CommitIndex' < sint.Z index ↔ (st.s (uint.nat i)).commitIndex < sint.Z index := by
    rw [Hf.2.2.2.2.1]
  by_cases hA : (st.s (uint.nat i)).commitIndex < sint.Z index
  rotate_left
  · rw [decide_eq_false (fun e => hA (hci.1 e))]
    cf_none (by unfold State.conflictAppendEntriesRequest; simp [hne, hA]; rfl)
  rw [decide_eq_true (hci.2 hA)]
  wp_auto
  wp_apply wp_HasNoConflict p st i index gm.Entries' m.entries $$ [Hst]
  · iframe Hst
    isplitl []
    · iunfold logRO; iexists fs; iframe Hfs Hfl
    ipureintro; exact ⟨Hi, hx1, hx2, hll, hel⟩
  cases hnc : st.hasNoConflict (uint.nat i) (sint.Z index) m.entries
  rotate_left
  · cf_none (by unfold State.conflictAppendEntriesRequest; simp [hne, hA, hnc]; rfl)
  wp_auto
  wp_apply wp_clone p st $$ [Hst] as %t Ht
  · iexact Hst
  try wp_auto
  mut_open t, st, [], i, Ht
  try wp_auto
  cases hs : subSeq (st.s (uint.nat i)).log 1 (((st.s (uint.nat i)).log.length : Int) - 1) with
  | none =>
    exfalso; unfold subSeq at hs; split at hs
    · cases hs
    · split at hs
      · omega
      · cases hs
  | some r =>
  wp_apply wp_SubSeq _ _ _ _ r $$ [Hlog] as %u #Hu
  · iframe Hlog; ipureintro
    rw [show sint.Z (W64 1) = 1 from rfl, show sint.Z (gs.Log'.len - W64 1) = ((st.s (uint.nat i)).log.length : Int) - 1 by rw [← hlen]; word]
    exact hs
  try wp_auto
  close_copy' { gc with Log' := u }, (fun (v : Server) => { v with log := r }), Hcf with Hu Hcr Hcg Hcc Hcd
  imod stateOwn_persist $$ Hs with #Hs
  imodintro
  iapply HΦ
  have : st.conflictAppendEntriesRequest (uint.nat i) (sint.Z index) m = .ok (some (st.upd (uint.nat i) (fun (v : Server) => { v with log := r }))) := by
    unfold State.conflictAppendEntriesRequest subSeqM; simp [hne, hA, hnc, hs]; rfl
  rw [this]
  iexact Hs

end proof

end Etcdraft
end EtcdGrove
end Perennial
