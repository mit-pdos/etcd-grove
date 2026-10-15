/-
Port of `election_proof/proof_raft__restore.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__restore
public import Spec.go_etcd_io.raft.v3.raftLog__matchTerm
public import Spec.go_etcd_io.raft.v3.raftLog__lastEntryID
public import Spec.go_etcd_io.raft.v3.raftLog__commitTo
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raftLog__restore
public import Spec.go_etcd_io.raft.v3.tracker.MakeProgressTracker
public import Spec.go_etcd_io.raft.v3.confchange.Restore
public import Spec.go_etcd_io.raft.v3.raft__switchToConfig
public import Spec.go_etcd_io.raft.v3.assertConfStatesEquivalent
public import Proof.go_etcd_io.raft.v3.InvApplyConfC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A list without repeats is a permutation of the elements of its set. -/
theorem perm_elements_listToSet (l : List w64) (h : l.Nodup) :
    l ≡ₚ GMap.elements (GMap.listToSet l) := by
  refine (List.perm_ext_iff_of_nodup h (GMap.NoDup_elements _)).2 ?_
  intro k; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]

theorem gset_size_union_le (X Y : GSet w64) :
    GMap.size (X ∪ Y) ≤ GMap.size X + GMap.size Y := by
  rw [GMap.size_union_alt]
  have := GMap.subseteq_size (GMap.difference_subseteq Y X)
  omega

/-- The progress map `Restore` builds for the lists `cl` has at most as many entries as the
lists have ids. -/
theorem restore_prs_size (cl : CSLists) (Hvnd : cl.voters.Nodup) (Hlnd : cl.learners.Nodup)
    (Hond : cl.outgoing.Nodup)
    (Hsz : (cl.voters.length + cl.learners.length + cl.outgoing.length + cl.learnersNext.length :
      Int) ≤ 2 ^ 62)
    (prs : GMap w64 Loc) (al : Bool)
    (Hprs : domSet prs =
      domSet (cfgStateC (csCfgM cl.outgoing cl.voters cl.learners cl.learnersNext al)).prs) :
    (GMap.size prs : Int) ≤ 2 ^ 62 := by
  have Hd : domSet prs = (GMap.listToSet cl.voters ∪ GMap.listToSet cl.outgoing) ∪
      GMap.listToSet cl.learners := by
    rw [Hprs]
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom']
    simp only [cfgStateC, csCfgM, CfgM.voters]
    rw [cfgFlags_mem]
    simp only [GMap.elem_of_union]
  have h1 := GMap.size_dom prs
  rw [Hd] at h1
  have h2 := gset_size_union_le (GMap.listToSet cl.voters ∪ GMap.listToSet cl.outgoing)
    (GMap.listToSet cl.learners)
  have h3 := gset_size_union_le (GMap.listToSet cl.voters) (GMap.listToSet cl.outgoing)
  rw [GMap.size_list_to_set _ Hvnd, GMap.size_list_to_set _ Hond] at h3
  rw [GMap.size_list_to_set _ Hlnd] at h2
  have : (0 : Int) ≤ cl.learnersNext.length := by omega
  omega

/-- What `confchange.Restore` builds for a `ConfState` denoting `c`, as `switchToConfig` takes
it (`ownConfigC`): its `Progress` values are some `pvs` whose learner flags are `c`'s. -/
theorem ownConfigC_of_restore (c : CfgM) (cfgv : tracker.Config) (prsm : Loc)
    (prs : GMap w64 Loc) (Hinv : CfgInv (cfgStateC c))
    (Hdom : domSet prs = domSet (cfgStateC c).prs) (Hsz : (GMap.size prs : Int) ≤ 2 ^ 62)
    (P : w64 → Progress → Prop) (HP : ∀ k p, P k p → (cfgStateC c).prs !! k = some p.learner) :
    ⊢ ownCfgCC (GF := GF) cfgv (DFrac.own 1) c -∗ prsm ↦$□ prs -∗
      ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress pr p ∗ ⌜P k p⌝) -∗
      ∃ pvs, ownConfigC c cfgv prsm prs pvs := by
  iintro Hc #Hprsm Hprogs
  ihave Hprogs : ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress (GF := GF) pr p ∗
      ⌜(cfgStateC c).prs !! k = some p.learner⌝) $$ [Hprogs]
  · iapply BigSepM.bigSepM_mono ?_ $$ Hprogs
    intro k pr _
    iintro ⟨%p, Hp, %Hpk⟩
    iexists p
    iframe Hp
    ipureintro; exact HP k p Hpk
  icases bigSepM_exist_sepM2 prs
    (fun k pr (p : Progress) => iprop(ownProgress (GF := GF) pr p ∗
      ⌜(cfgStateC c).prs !! k = some p.learner⌝))
    $$ Hprogs with ⟨%pvs, Hprogs⟩
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ Hprogs with ⟨Hprogs, Hfl⟩
  ihave %Hfl := BigSepM2.bigSepM2_pure_intro $$ Hfl
  -- the learner flags of `pvs` are the configuration's
  have Htf : trkFlags pvs = (cfgStateC c).prs := by
    apply GMap.map_eq; intro k
    rw [trkFlags_lookup]
    cases hp : pvs !! k with
    | some p =>
      obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1
        ((Hiff k).2 (by show (pvs !! k).isSome = true; rw [hp]; rfl))
      exact (Hfl k pr p hpr hp).symm
    | none =>
      cases hc : (cfgStateC c).prs !! k with
      | none => rfl
      | some b =>
        exfalso
        have hk : k ∈ domSet prs := by
          rw [Hdom, GMap.elem_of_dom', GMap.mem_iff, hc]; rfl
        rw [GMap.elem_of_dom', GMap.mem_iff] at hk
        have h2 : (pvs !! k).isSome = true := (Hiff k).1 hk
        rw [hp] at h2
        exact absurd h2 (by decide)
  iexists pvs
  unfold ownConfigC
  iframe Hc Hprsm Hprogs
  ipureintro
  refine ⟨?_, ?_, ?_, Hsz⟩
  · rw [Htf]; exact Hinv
  · rw [Hdom]
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom']
    simp only [cfgStateC, CfgM.ids]
    rw [cfgFlags_mem, GMap.elem_of_union]
  · intro k p hp
    have h1 : (cfgStateC c).prs !! k = some p.learner := by
      rw [← Htf, trkFlags_lookup, hp]; rfl
    simp only [cfgStateC] at h1
    rw [cfgFlags_lookup] at h1
    by_cases hv : k ∈ c.voters
    · rw [ite_eq_left hv] at h1
      have hl : k ∉ c.learners := by
        intro hl
        obtain ⟨ho, hi, -⟩ := Hinv.2.2.1 k hl
        unfold CfgM.voters at hv
        rcases (GMap.elem_of_union _ _ _).1 hv with h | h
        · exact hi h
        · exact ho h
      rw [← Option.some.inj h1]; simp [hl]
    · rw [ite_eq_right hv] at h1
      by_cases hl : k ∈ c.learners
      · rw [ite_eq_left hl] at h1; rw [← Option.some.inj h1]; simp [hl]
      · rw [ite_eq_right hl] at h1; cases h1

/-- `restore`'s `found` search has not met `id` in the first `k` of its three sets
(`[Voters, Learners, VotersOutgoing]`). -/
def FoundBefore (cl : CSLists) (id : w64) (k : Nat) : Prop :=
  ∀ (j : Nat) (L : List w64), j < k → [cl.voters, cl.learners, cl.outgoing][j]? = some L →
    id ∉ L

theorem foundBefore_zero (cl : CSLists) (id : w64) : FoundBefore cl id 0 :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem foundBefore_succ {cl : CSLists} {id : w64} {k : Nat} {L : List w64}
    (H : FoundBefore cl id k) (HL : [cl.voters, cl.learners, cl.outgoing][k]? = some L)
    (Hn : id ∉ L) : FoundBefore cl id (k + 1) := by
  intro j L' hj hL'
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
  · exact H j L' h hL'
  · subst h; rw [HL] at hL'; cases hL'; exact Hn

theorem foundBefore_three {cl : CSLists} {id : w64} (H : FoundBefore cl id 3)
    (Hin : id ∈ cl.voters ∨ id ∈ cl.learners ∨ id ∈ cl.outgoing) : False := by
  rcases Hin with h | h | h
  · exact H 0 _ (by decide) rfl h
  · exact H 1 _ (by decide) rfl h
  · exact H 2 _ (by decide) rfl h

/-- The `k`-th set `found` searches, read-only. -/
theorem csl_found_slice (cs : raftpb.ConfState) (cl : CSLists) (k : Nat) (hk : k < 3) :
    ownCSL (GF := GF) cs cl ⊢ ∃ (sl : GoSlice) (L : List w64),
      ⌜[cs.Voters', cs.Learners', cs.VotersOutgoing'][k]? = some sl ∧
        [cl.voters, cl.learners, cl.outgoing][k]? = some L⌝ ∗ sl ↦*□ L := by
  unfold ownCSL
  iintro ⟨#Hv, #Hl, #Ho, -⟩
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · iexists cs.Voters', cl.voters
    iframe Hv; ipureintro; exact ⟨rfl, rfl⟩
  · iexists cs.Learners', cl.learners
    iframe Hl; ipureintro; exact ⟨rfl, rfl⟩
  · iexists cs.VotersOutgoing', cl.outgoing
    iframe Ho; ipureintro; exact ⟨rfl, rfl⟩

/-- The body's exits in order (`raft.restore.impl`):

- `Index <= committed`: `false`;
- `state != StateFollower`: dead (`s.role = .follower`);
- the `found` search over `[Voters; Learners; VotersOutgoing]`: `id` is in one of them
  (since 2026-10-14, stage B8; until then among the voters), so the inner loop breaks in some
  set and the outer loop right after it (`FoundBefore`: no earlier set has it); the `!found`
  arm is dead;
- `matchTerm(id)`: `lastEntryID`, an `Infof`, `commitTo(Index)` (in range: `Index` has
  a term in the log) and `false`;
- otherwise `raftLog.restore(s)`; the tracker replaced by the empty one
  `MakeProgressTracker` builds -- `ownRaftPhys` at the empty configuration, as in
  `newRaft` (`ownRaftPhys_retrack`, `ownTracker_empty`; the tally was already empty,
  `s.votes = ∅`); `confchange.Restore` on it, its `v0` read back out of the empty
  tracker; then `switchToConfig` to the snapshot's configuration and `assertConfStatesEquivalent`;
  `lastEntryID`, an `Infof` and `true`. -/
theorem raft.restore.wp_proof
    (wp_raftLog_matchTerm : raftLog.matchTerm.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG))
    (wp_raftLog_commitTo : raftLog.commitTo.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_restore : raftLog.restore.spec (GF := GF) (hG := hG))
    (wp_MakeProgressTracker : tracker.MakeProgressTracker.spec (GF := GF) (hG := hG))
    (wp_confchange_Restore : confchange.Restore.spec (GF := GF) (hG := hG))
    (wp_raft_switchToConfig : raft.switchToConfig.spec (GF := GF) (hG := hG))
    (wp_assertConfStatesEquivalent : assertConfStatesEquivalent.spec (GF := GF) (hG := hG)) :
    raft.restore.spec (GF := GF) (hG := hG) := by
  intro c r id s sv cl Hrole Hvotes Hidv Hscope
  obtain ⟨Hwf, Hvnd, Hlnd, Hond, Hnnd, Hsz, Hal0, Hidx61⟩ := Hscope
  wp_start as H
  iNamed H
  unfold ownCSL
  icases Hcs with ⟨#Hvoters, #Hlearners, #Houtg, #Hlnx⟩
  wp_auto
  -- `s.Metadata.Index <= r.raftLog.committed`
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_struct $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hlogback $$ Hlog
  obtain ⟨Hcm, -⟩ := Hlv
  rw [Hcm]
  by_cases Hst : uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.committed
  · -- obsolete
    rw [decide_eq_true Hst]
    wp_auto
    iapply HΦ $$ %false %s
    simp only [restoreCfg, Bool.false_eq_true, ↓reduceIte]
    iframe Hphys
    ipureintro
    exact .inl ⟨Hst, rfl, rfl⟩
  rw [decide_eq_false Hst]
  wp_auto
  -- `r.state != StateFollower`: a follower
  wp_apply raft.wp_load_stateC $$ Hphys as Hphys
  rw [Hrole, decide_eq_true (show stateW64 PRole.follower = W64 0 from rfl)]
  wp_auto
  -- the `found` search over `[Voters; Learners; VotersOutgoing]`
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %rsl ⟨Hrsl, -⟩
  simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl,
    List.set_cons_succ, List.set_cons_zero]
  wp_auto
  ihave %Hrlen := ownSlice_len $$ Hrsl
  simp only [List.length_cons, List.length_nil] at Hrlen
  -- the outer loop: no set before the current one has `id`; `id` is in one of the three
  -- (`Hidv`), so the inner loop finds it in some set, breaking both
  ihave IH : (∃ (k : w64) (st : GoSlice),
      "i" ∷ i_ptr ↦ k ∗ "set" ∷ set_ptr ↦ st ∗ "found" ∷ found_ptr ↦ false ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 3 ∧ FoundBefore cl id (sint.Z k).toNat⌝) $$ [i set found]
  · iexists W64 0, zero_val GoSlice
    iframe i set found
    ipureintro; exact ⟨by word, by word, foundBefore_zero cl id⟩
  wp_for IH
  obtain ⟨Hk0, Hk3, Hkb⟩ := Hk
  wp_if_destruct
  rotate_left
  · -- the three sets ran out without `id`: impossible
    exfalso
    have Hk3' : (sint.Z k).toNat = 3 := by
      have : ¬ sint.Z k < 3 := by word
      omega
    rw [Hk3'] at Hkb
    exact foundBefore_three Hkb Hidv
  have Hk3' : (sint.Z k).toNat < 3 := by
    have : sint.Z k < 3 := by word
    omega
  icases csl_found_slice sv.Metadata'.ConfState' cl (sint.Z k).toNat Hk3' $$ [Hvoters Hlearners
      Houtg Hlnx] with ⟨%sl, %L, %HsL, #HL⟩
  · unfold ownCSL; iframe Hvoters Hlearners Houtg Hlnx
  obtain ⟨Hsl, HLk⟩ := HsL
  rw [ite_eq_left]
  rotate_left
  · exact ⟨Hk0, by word⟩
  wp_apply wp_load_slice_index (V := GoSlice) (t := go.uint64.SliceType) _ (sint.Z k) _ _
      sl Hk0 $$ [$Hrsl] as Hrsl
  · ipureintro; exact Hsl
  ihave %Hvlen := ownSlice_len $$ HL
  ihave IH2 : (∃ (k2 x : w64),
      "i" ∷ i_ptr ↦ k2 ∗ "id" ∷ id_ptr ↦ x ∗ "found" ∷ found_ptr ↦ false ∗
      "%Hk2" ∷ ⌜(0 ≤ sint.Z k2 ∧ sint.Z k2 ≤ (L.length : Int)) ∧
                id ∉ L.take (sint.Z k2).toNat⌝) $$ [i id found]
  · iexists W64 0, zero_val w64
    iframe i id found
    ipureintro
    exact ⟨⟨by word, by word⟩, by simp⟩
  wp_for IH2
  obtain ⟨Hk2b, Hk2n⟩ := Hk2
  wp_if_destruct
  rotate_left
  · -- this set ran out without `id`: on to the next one
    have HnL : id ∉ L := by
      have := Hk2n
      rwa [List.take_of_length_le (by word)] at this
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [show (sint.Z (k + W64 1)).toNat = (sint.Z k).toNat + 1 by word]
    exact foundBefore_succ Hkb HLk HnL
  list_elem L (sint.Z k2).toNat as y
  rw [ite_eq_left (show 0 ≤ sint.Z k2 ∧ sint.Z k2 < sint.Z sl.len by word)]
  wp_apply wp_load_slice_index (V := w64) (t := go.uint64) _ (sint.Z k2) L _ y
      (by omega) $$ [$HL] as -
  · ipureintro; exact Hy_lookup
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  by_cases Hne : y = id
  rotate_left
  · -- not this one: next
    rw [decide_eq_false Hne]
    wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_⟩
    rw [show (sint.Z (k2 + W64 1)).toNat = (sint.Z k2).toNat + 1 by word,
      List.take_add_one, Hy_lookup]
    simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
    exact ⟨Hk2n, fun h => Hne h.symm⟩
  -- found: break the inner loop, then the outer one
  subst y
  rw [decide_eq_true rfl]
  wp_auto
  wp_for_post
  wp_for_post
  -- `matchTerm(id)`
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
  wp_apply wp_raftLog_matchTerm _ _ { term' := sv.Metadata'.Term', index' := sv.Metadata'.Index' }
    $$ [$Hlog] as %b ⟨Hlog, %Hb⟩
  ihave Hphys := Hlogback $$ Hlog
  change b = decide (PlogMatches _ _ (snapId sv)) at Hb
  by_cases Hm : PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (snapId sv)
  · -- the log has the snapshot's last entry: fast-forward the commit
    rw [Hb, decide_eq_true Hm]
    wp_auto
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_apply wp_raftLog_lastEntryID $$ [$Hlog] as %last ⟨Hlog, -⟩
    ihave Hphys := Hlogback $$ Hlog
    -- the `Infof`: `r.id`, `r.raftLog.committed`, the two ids
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv2, Hl, -, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    wp_raft_logC
    -- `commitTo(Index)`: in range, the log has a term at `Index`
    obtain ⟨-, Hle⟩ := plogTermAt_some_range _ _ _ _ Hm
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_at $$ Hphys with ⟨Hlog, %Hgh0, Hlogback⟩
    wp_apply wp_raftLog_commitTo _ _ sv.Metadata'.Index' Hle $$ [$Hlog] as Hlog
    ihave Hphys := Hlogback $$ Hlog %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl)
    iapply HΦ $$ %false %_
    simp only [restoreCfg, Bool.false_eq_true, ↓reduceIte]
    iframe Hphys
    ipureintro
    refine .inr (.inl ⟨by simp only [snapId]; omega, Hm, rfl, ?_⟩)
    simp only [plogCommitTo, snapId] at *
    rw [ite_eq_left (by omega)]
  · rw [Hb, decide_eq_false Hm]
    wp_auto
    -- `r.raftLog.restore(s)`
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_at $$ Hphys with ⟨Hlog, -, Hlogback⟩
    ihave #Hcs : ownCSL (GF := GF) sv.Metadata'.ConfState' cl $$ []
    · unfold ownCSL; iframe Hvoters Hlearners Houtg Hlnx
    wp_apply wp_raftLog_restore _ _ sv cl (by simp only [snapId]; omega)
        (by simp only [snapId]; omega) $$ [$Hlog $Hcs] as Hlog
    ihave Hphys := Hlogback $$ %_ Hlog %(LogGhOk.of_snap (by simp [logRestore]))
    -- the tracker replaced by the empty one, the log used meanwhile
    icases ownRaftPhysC_retrack c c.voters (CfgM.simple ∅ (domSet (∅ : GMap w64 Loc) \ ∅)).voters
        (c := CfgM.simple ∅ (domSet (∅ : GMap w64 Loc) \ ∅)) _ _ _
        (by intro h; exact absurd Hrole h) $$ Hphys with ⟨%tv, Htrkf, Htrk, Hlf, Hlog, Hback⟩
    icases ownTrackerC_maxinflight $$ Htrk with ⟨%Hmi, -⟩
    wp_auto
    wp_apply wp_MakeProgressTracker as %tv0 %v0 ⟨%Htv0, Hv0, Hvotes0, Hprs0⟩
    obtain ⟨Htv0mi, Htv0mb, Htv0arr, Htv0l, Htv0ln, Htv0al⟩ := Htv0
    wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, -⟩
    -- `confchange.Restore`: the empty tracker, the snapshot's `ConfState`, which it answers
    -- exactly (`restoreM_wf`)
    ipersist Hprs0
    have Hmi0 : 0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62 := by
      rw [Htv0mi]; exact Hmi
    have Hvne : cl.voters ≠ [] := Hwf.1
    have Hrm := restoreM_wf cl.outgoing cl.voters cl.learners cl.learnersNext
      sv.Metadata'.ConfState'.AutoLeave' Hwf
    have Hinv := restoreM_cfgInv Hrm
    ihave Hl1 : ownIdList (GF := GF) sv.Metadata'.ConfState'.Learners' DFrac.discard cl.learners
      $$ []
    · unfold ownIdList; iright; iexact Hlearners
    ihave Ho1 : ownIdList (GF := GF) sv.Metadata'.ConfState'.VotersOutgoing' DFrac.discard
      cl.outgoing $$ []
    · unfold ownIdList; iright; iexact Houtg
    ihave Hn1 : ownIdList (GF := GF) sv.Metadata'.ConfState'.LearnersNext' DFrac.discard
      cl.learnersNext $$ []
    · unfold ownIdList; iright; iexact Hlnx
    wp_apply wp_confchange_Restore { Tracker' := tv0, LastIndex' := li } _ cl.voters cl.learners
        cl.outgoing cl.learnersNext DFrac.discard DFrac.discard DFrac.discard DFrac.discard v0 _
        Hvne Hrm Hmi0 Htv0arr Htv0l Htv0ln Htv0al
        $$ [$Hvoters $Hl1 $Ho1 $Hn1 $Hv0 $Hprs0]
      as %cfgv %prsm %prs ⟨-, -, -, -, Hv0, -, Hcfg, Hprsm, %Hprs, Hprogs⟩
    -- the configuration `Restore` built, as `switchToConfig` takes it
    ipersist Hprsm
    have Hsz' : (GMap.size prs : Int) ≤ 2 ^ 62 :=
      restore_prs_size cl Hvnd Hlnd Hond Hsz prs sv.Metadata'.ConfState'.AutoLeave' Hprs
    ihave Hprogs : ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress (GF := GF) pr p ∗
        ⌜(cfgStateC (csCfgM cl.outgoing cl.voters cl.learners cl.learnersNext
          sv.Metadata'.ConfState'.AutoLeave')).prs !! k = some p.learner⌝) $$ [Hprogs]
    · iapply BigSepM.bigSepM_mono ?_ $$ Hprogs
      intro k pr _
      iintro ⟨%p, Hp, %Hpk⟩
      iexists p
      iframe Hp
      ipureintro
      simpa [cfgStateC, cfgFlags, csCfgM, CfgM.voters] using Hpk
    icases ownConfigC_of_restore (snapCfg sv cl) cfgv prsm prs Hinv Hprs Hsz' _ (fun _ _ h => h) $$ Hcfg Hprsm Hprogs
      with ⟨%pvs, Hnew⟩
    -- the struct, re-sealed over the empty configuration
    ihave Htrk0 := ownTracker_empty tv0 v0 Htv0arr Htv0l Htv0ln Htv0al Hmi0 $$ Hv0 Hvotes0 Hprs0
    ihave Htrk0 := ownTracker_toC _ _ _ $$ Htrk0
    ihave Hphys := Hback $$ %tv0 %∅ %∅ %∅ %_ Hlf Htrkf Htrk0 Hlog
      %(LogGhOk.of_snap (by simp [logRestore]))
    generalize HS1 : ({ s with votes := ∅, progress := ∅, prvals := ∅, logst := logRestore s.logst (snapTrip sv cl) } : NState) = s1
    have Hrole1 : s1.role = .follower := by rw [← HS1]; exact Hrole
    -- `assertConfStatesEquivalent(r.logger, cs, r.switchToConfig(cfg, trk))`
    wp_apply raft.wp_load_loggerC $$ Hphys as %lok0 ⟨Hphys, #Hlg0⟩
    icases ownRaftPhysCV_reconfig _ (snapCfg sv cl) ((snapCfg sv cl).voters ∪ {[id]}) r id s1
        (fun h => absurd Hrole1 h) $$ Hphys with ⟨%tv1, Htrkf, Hold, Hback2⟩
    icases ownTrackerC_votes $$ Hold with ⟨Hvotes, %Hmi1⟩
    wp_apply wp_raft_switchToConfig (snapCfg sv cl) r id s1 tv1 cfgv prsm prs pvs
        (fun h => absurd (Hrole1.symm.trans h) (by decide))
        (fun h => by rcases h with h | h <;> rw [Hrole1] at h <;> cases h)
      $$ [$Htrkf $Hback2 $Hvotes $Hnew]
      as %cs2 %xs2 %os2 %ls2 %lns2 %s2 ⟨Hphys, Hcs2v, Hcs2o, Hcs2l, Hcs2n, %Hcs2, %Hsw⟩
    · ipureintro; exact Hmi1
    obtain ⟨Hxs2, Hos2, Hls2, Hlns2, Hc2al⟩ := Hcs2
    unfold SwitchOkC at Hsw
    rw [ite_eq_right (by simp [Hrole1])] at Hsw
    subst Hsw
    -- the snapshot's lists against the configuration's sets
    have Hperm : cl.Perm ⟨xs2, ls2, os2, lns2⟩ := by
      refine ⟨(perm_elements_listToSet _ Hvnd).trans Hxs2.symm,
        (perm_elements_listToSet _ Hlnd).trans Hls2.symm,
        (perm_elements_listToSet _ Hond).trans Hos2.symm,
        (perm_elements_listToSet _ Hnnd).trans Hlns2.symm⟩
    have Hbnd : cl.Bounded := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    ihave Hids2 : ownCSIds (GF := GF) cs2 (DFrac.own 1) (DFrac.own 1) ⟨xs2, ls2, os2, lns2⟩
      $$ [Hcs2v Hcs2o Hcs2l Hcs2n]
    · unfold ownCSIds ownIdList
      iframe Hcs2v
      isplitl [Hcs2l]
      · iright; iexact Hcs2l
      isplitl [Hcs2o]
      · iright; iexact Hcs2o
      iright; iexact Hcs2n
    ihave #Hids1 := ownCSL_ids sv.Metadata'.ConfState' cl $$ [Hvoters Hlearners Houtg Hlnx]
    · unfold ownCSL; iframe Hvoters Hlearners Houtg Hlnx
    have Hal2 : sv.Metadata'.ConfState'.AutoLeave' = cs2.AutoLeave' := by
      rw [Hc2al]
      unfold snapCfg csCfgM
      by_cases ho : cl.outgoing = []
      · simp only [ho, ↓reduceIte]; exact Hal0 ho
      · simp only [ho, ↓reduceIte]
    wp_apply wp_assertConfStatesEquivalent _ _ cs2 cl ⟨xs2, ls2, os2, lns2⟩ DFrac.discard
        (DFrac.own 1) DFrac.discard (DFrac.own 1) Hperm Hbnd Hal2 $$ [$Hids1 $Hids2] as -
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_apply wp_raftLog_lastEntryID $$ [$Hlog] as %last ⟨Hlog, -⟩
    ihave Hphys := Hlogback $$ Hlog
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv3, Hl, -, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    wp_raft_logC
    iapply HΦ $$ %true %_
    simp only [restoreCfg, ↓reduceIte]
    iframe Hphys
    ipureintro
    refine .inr (.inr ⟨by simp only [snapId]; omega, Hm, rfl, prs, pvs,
      learnerOfC (snapCfg sv cl) id, ?_⟩)
    subst HS1
    obtain ⟨⟩ := s
    simp only at Hvotes
    subst Hvotes
    rfl

end proof

end EtcdGrove
end Perennial
