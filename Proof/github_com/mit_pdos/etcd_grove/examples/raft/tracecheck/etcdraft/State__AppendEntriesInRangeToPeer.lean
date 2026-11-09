/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__AppendEntriesInRangeToPeer`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__AppendEntriesInRangeToPeer
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__send
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__GetConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__GetLearners
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Union
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Has
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
local macro "ae_none" : tactic => `(tactic| (
    try wp_auto
    imodintro
    iapply HΦ
    have hn : st.appendEntriesInRangeToPeer sub (uint.nat i) (uint.nat j) (sint.Z b) (sint.Z e) = .ok none := by
      unfold State.appendEntriesInRangeToPeer; simp_all; rfl
    rw [hn] at Ho
    cases Ho
    ipureintro; rfl))

theorem State.AppendEntriesInRangeToPeer.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_send : State.send.spec (GF := GF) (hG := hG))
    (wp_GetConfig : State.GetConfig.spec (GF := GF) (hG := hG))
    (wp_GetLearners : State.GetLearners.spec (GF := GF) (hG := hG))
    (wp_Union : Set.Union.spec (GF := GF) (hG := hG))
    (wp_Has : Set.Has.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG)) :
    State.AppendEntriesInRangeToPeer.spec (GF := GF) (hG := hG) := by
  intro p st gsub sub i j b e o
  wp_start as ⟨#Hst, %Hsub, %Hi, %Hpok, %hb1, %hb2, %he1, %he2, %Ho⟩
  read_server
  iapply wp_fupd
  wp_auto
  lookup_server
  have hij : i = j ↔ uint.nat i = uint.nat j := ⟨fun h => h ▸ rfl, fun h => word.unsigned_inj (by exact_mod_cast h)⟩
  by_cases h1 : uint.nat i = uint.nat j
  · rw [decide_eq_true (hij.2 h1)]; ae_none
  rw [decide_eq_false (fun e => h1 (hij.1 e))]
  wp_auto
  by_cases h2 : sint.Z e < sint.Z b
  · rw [decide_eq_true h2]; ae_none
  rw [decide_eq_false h2]
  wp_auto
  try simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Leader]
  rw [decide_strRel Hf.2.1 strRel_leader]
  by_cases h3 : (st.s (uint.nat i)).state = leader
  rotate_left
  · rw [decide_eq_false h3]; ae_none
  rw [decide_eq_true h3]
  wp_auto
  wp_apply wp_GetLearners p st i $$ [Hst] as %sl1 #Hsl1
  · iframe Hst; ipureintro; exact Hi
  try wp_auto
  wp_apply wp_GetConfig p st i $$ [Hst] as %sl2 #Hsl2
  · iframe Hst; ipureintro; exact Hi
  try wp_auto
  wp_apply wp_Union _ _ _ _ $$ [Hsl1 Hsl2] as %sl3 #Hsl3
  · iframe Hsl1 Hsl2
  try wp_auto
  wp_apply wp_Has _ _ j $$ [Hsl3]
  · iexact Hsl3
  iintro -
  try wp_auto
  by_cases h4 : uint.nat j ∈ (st.getConfig (uint.nat i)).union (st.getLearners (uint.nat i))
  rotate_left
  · rw [decide_eq_false h4]
    have h4' : ((st.getConfig (uint.nat i)).union (st.getLearners (uint.nat i))).contains (uint.nat j) = false := by
      simpa using h4
    ae_none
  rw [decide_eq_true h4]
  wp_auto
  have hlen : sint.Z gs.Log'.len = ((st.s (uint.nat i)).log.length : Int) := by rw [← Hell, Hesl.1]; word
  have hpli : sint.Z (b - W64 1) = sint.Z b - 1 := by word
  ipersist v
  ipersist prevLogIndex
  wp_join iprop(∃ pt : w64, prevLogTerm_ptr ↦ pt ∗ ⌜sint.Z pt = (if sint.Z b - 1 > 0 && sint.Z b - 1 ≤ (st.s (uint.nat i)).log.length then (((st.s (uint.nat i)).log[(sint.Z b - 1 - 1).toNat]?).map Entry.term).getD 0 else 0)⌝) at (if: _ then _ else _) with [prevLogTerm] as ⟨%pt, prevLogTerm, %Hpt⟩
  · rw [hpli]
    by_cases c1 : 0 < sint.Z b - 1
    rotate_left
    · rw [decide_eq_false (by simpa using c1)]
      wp_auto
      wp_join_done
      iexists _
      iframe
      ipureintro
      split
      · rename_i hh; simp at hh; omega
      · rfl
    rw [decide_eq_true (by simpa using c1)]
    wp_auto
    by_cases c2 : sint.Z b - 1 ≤ (st.s (uint.nat i)).log.length
    rotate_left
    · rw [decide_eq_false (show ¬ (sint.Z (b - W64 1) ≤ sint.Z gs.Log'.len) by rw [hpli, hlen]; exact c2)]
      wp_auto
      wp_join_done
      iexists _
      iframe
      ipureintro
      split
      · rename_i hh; simp at hh; omega
      · rfl
    rw [decide_eq_true (show sint.Z (b - W64 1) ≤ sint.Z gs.Log'.len by rw [hpli, hlen]; exact c2)]
    wp_auto
    have hk2 : sint.Z (b - W64 1 - W64 1) = sint.Z b - 2 := by word
    have hk0 : 0 ≤ sint.Z (b - W64 1 - W64 1) ∧ sint.Z (b - W64 1 - W64 1) < sint.Z gs.Log'.len := by
      rw [hk2, hlen]; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hk0)]
    have hidx : (sint.Z b - 1 - 1).toNat = (sint.Z (b - W64 1 - W64 1)).toNat := by rw [hk2, show sint.Z b - 1 - 1 = sint.Z b - 2 by omega]
    have hkn : (sint.Z (b - W64 1 - W64 1)).toNat < es.length := by rw [Hell]; rw [hk2]; omega
    obtain ⟨x, Hx⟩ : ∃ x, es[(sint.Z (b - W64 1 - W64 1)).toNat]? = some x := ⟨_, List.getElem?_eq_getElem hkn⟩
    obtain ⟨y, Hy⟩ : ∃ y, (st.s (uint.nat i)).log[(sint.Z (b - W64 1 - W64 1)).toNat]? = some y :=
      ⟨_, List.getElem?_eq_getElem (Hell ▸ hkn)⟩
    ihave #Hxy := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hx Hy $$ Hel
    iunfold entryRO at Hxy
    icases Hxy with ⟨%Hxy1, -⟩
    icases ownSlice_elem_acc _ x _ _ es hk0.1 Hx $$ Hes with ⟨#Hxe, -⟩
    icases typedPointsto_split _ _ _ $$ Hxe with Hxef
    simp only [TypedPointsto.typedPointstoDef]
    icases Hxef with ⟨#E1, #E2, #E3, -⟩
    wp_auto
    wp_join_done
    iexists _
    iframe
    ipureintro
    rw [Hxy1.1]
    have hc : (decide (sint.Z b - 1 > 0) && decide (sint.Z b - 1 ≤ ((st.s (uint.nat i)).log.length : Int))) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨c1, c2⟩
    simp only [hc, ↓reduceIte]
    rw [hidx, Hy]
    rfl
  wp_apply wp_min_int
  try wp_auto
  have hle : sint.Z (if sint.Z gs.Log'.len < sint.Z (e - W64 1) then gs.Log'.len else e - W64 1) = (min ((st.s (uint.nat i)).log.length : Int) (sint.Z e - 1)) := by
    rw [sint_min, hlen, show sint.Z (e - W64 1) = sint.Z e - 1 by word]
  cases hs : subSeq (st.s (uint.nat i)).log (sint.Z b) (min ((st.s (uint.nat i)).log.length : Int) (sint.Z e - 1)) with
  | none =>
    exfalso
    unfold State.appendEntriesInRangeToPeer subSeqM at Ho
    simp [h1, h2, h3, h4, hs] at Ho
    cases Ho
  | some r =>
  wp_apply wp_SubSeq _ _ _ _ r $$ [Hlog] as %ent #Hent
  · iframe Hlog; ipureintro; rw [hle]; exact hs
  try wp_auto
  ipersist lastEntry
  ipersist j
  ipersist subtype
  wp_join iprop(∃ c : w64, commit_ptr ↦ c ∗ ⌜sint.Z c = (if sub == "heartbeat" then min (st.s (uint.nat i)).commitIndex ((st.s (uint.nat i)).matchIndex (uint.nat j)) else if sub == "snapshot" then min (st.s (uint.nat i)).commitIndex (min ((st.s (uint.nat i)).log.length : Int) (sint.Z e - 1)) else (st.s (uint.nat i)).commitIndex)⌝) at (if: _ then _ else _) with [commit] as ⟨%cm, commit, %Hcm⟩
  · rw [decide_strRel Hsub strRel_heartbeat]
    by_cases s1 : sub = "heartbeat"
    · rw [decide_eq_true s1]
      wp_auto
      wp_apply wp_map_lookup1 $$ [Hmm] as -
      · iexact Hmm
      try wp_auto
      wp_apply wp_min_int
      try wp_auto
      wp_join_done
      iexists _
      iframe
      ipureintro
      rw [sint_min, Hf.2.2.2.2.1, show (zero_val w64 : w64) = W64 0 from rfl, Hmi j]
      simp [s1]
    rw [decide_eq_false s1]
    wp_auto
    rw [decide_strRel Hsub strRel_snapshot]
    by_cases s2 : sub = "snapshot"
    · rw [decide_eq_true s2]
      wp_auto
      wp_apply wp_min_int
      try wp_auto
      wp_join_done
      iexists _
      iframe
      ipureintro
      rw [sint_min, Hf.2.2.2.2.1, hle]
      simp [s1, s2]
    rw [decide_eq_false s2]
    wp_auto
    wp_join_done
    iexists _
    iframe
    ipureintro
    rw [Hf.2.2.2.2.1]
    simp [s1, s2]
  have ho : o = some (st.send { type := .appendEntriesRequest, subtype := sub, term := (st.s (uint.nat i)).currentTerm, prevLogIndex := sint.Z b - 1, prevLogTerm := (if sint.Z b - 1 > 0 && sint.Z b - 1 ≤ (st.s (uint.nat i)).log.length then (((st.s (uint.nat i)).log[(sint.Z b - 1 - 1).toNat]?).map Entry.term).getD 0 else 0), entries := r, commitIndex := (if sub == "heartbeat" then min (st.s (uint.nat i)).commitIndex ((st.s (uint.nat i)).matchIndex (uint.nat j)) else if sub == "snapshot" then min (st.s (uint.nat i)).commitIndex (min ((st.s (uint.nat i)).log.length : Int) (sint.Z e - 1)) else (st.s (uint.nat i)).commitIndex), source := uint.nat i, dest := uint.nat j }) := by
    have : st.appendEntriesInRangeToPeer sub (uint.nat i) (uint.nat j) (sint.Z b) (sint.Z e) = .ok (some (st.send { type := .appendEntriesRequest, subtype := sub, term := (st.s (uint.nat i)).currentTerm, prevLogIndex := sint.Z b - 1, prevLogTerm := (if sint.Z b - 1 > 0 && sint.Z b - 1 ≤ (st.s (uint.nat i)).log.length then (((st.s (uint.nat i)).log[(sint.Z b - 1 - 1).toNat]?).map Entry.term).getD 0 else 0), entries := r, commitIndex := (if sub == "heartbeat" then min (st.s (uint.nat i)).commitIndex ((st.s (uint.nat i)).matchIndex (uint.nat j)) else if sub == "snapshot" then min (st.s (uint.nat i)).commitIndex (min ((st.s (uint.nat i)).log.length : Int) (sint.Z e - 1)) else (st.s (uint.nat i)).commitIndex), source := uint.nat i, dest := uint.nat j })) := by
      unfold State.appendEntriesInRangeToPeer subSeqM; simp [h1, h2, h3, h4, hs]; rfl
    rw [this] at Ho; cases Ho; rfl
  wp_apply wp_clone p st $$ [Hst] as %t Ht
  · iexact Hst
  try wp_auto
  irename «$a0» => Hmq
  ipersist Hmq
  ihave #Hmsg : msgRO (GF := GF) «$a0_ptr» { type := .appendEntriesRequest, subtype := sub, term := (st.s (uint.nat i)).currentTerm, prevLogIndex := sint.Z b - 1, prevLogTerm := (if sint.Z b - 1 > 0 && sint.Z b - 1 ≤ (st.s (uint.nat i)).log.length then (((st.s (uint.nat i)).log[(sint.Z b - 1 - 1).toNat]?).map Entry.term).getD 0 else 0), entries := r, commitIndex := (if sub == "heartbeat" then min (st.s (uint.nat i)).commitIndex ((st.s (uint.nat i)).matchIndex (uint.nat j)) else if sub == "snapshot" then min (st.s (uint.nat i)).commitIndex (min ((st.s (uint.nat i)).log.length : Int) (sint.Z e - 1)) else (st.s (uint.nat i)).commitIndex), source := uint.nat i, dest := uint.nat j } $$ []
  · iunfold msgRO
    iexists _
    iframe Hmq Hent
    ipureintro
    exact ⟨rfl, Hsub, Hf.1, rfl, rfl, rfl, hpli, Hpt, Hcm, rfl, rfl, rfl, rfl⟩
  wp_apply wp_send t st [] _ _ $$ [Ht Hmsg] as Ht
  · iframe Ht Hmsg; ipureintro; exact ⟨Hpok.1, Hpok.count_lt _⟩
  try wp_auto
  imod stateOwn_persist $$ Ht with #Ht
  imodintro
  iapply HΦ
  rw [ho]
  iexact Ht

end proof

end Etcdraft
end EtcdGrove
end Perennial
