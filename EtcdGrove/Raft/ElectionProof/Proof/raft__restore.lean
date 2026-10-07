/-
Port of `election_proof/proof_raft__restore.v`.
-/
import EtcdGrove.Raft.ElectionProof.Spec.raft__restore
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__matchTerm
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__lastEntryID
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__commitTo
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__lastIndex
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__restore
import EtcdGrove.Raft.ElectionProof.Spec.MakeProgressTracker
import EtcdGrove.Raft.ElectionProof.Spec.confchange_Restore
import EtcdGrove.Raft.ElectionProof.Spec.raft__switchToConfig
import EtcdGrove.Raft.ElectionProof.Spec.assertConfStatesEquivalent

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The body's exits in order (`raft.restore.impl`):

- `Index <= committed`: `false`;
- `state != StateFollower`: dead (`s.role = .follower`);
- the `found` search over `[Voters; Learners; VotersOutgoing]`: `id` is among the
  voters (`SnapScope`, `id ∈ cfg`), so the inner loop breaks in the first set and the
  outer loop right after it; the `!found` arm is dead;
- `matchTerm(id)`: `lastEntryID`, an `Infof`, `commitTo(Index)` (in range: `Index` has
  a term in the log) and `false`;
- otherwise `raftLog.restore(s)`; the tracker replaced by the empty one
  `MakeProgressTracker` builds -- `ownRaftPhys` at the empty configuration, as in
  `newRaft` (`ownRaftPhys_retrack`, `ownTracker_empty`; the tally was already empty,
  `s.votes = ∅`); `confchange.Restore` on it, its `v0` read back out of the empty
  tracker; then `switchToConfig` back to `cfg` and `assertConfStatesEquivalent`;
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
  intro cfg r id s sv voters Hrole Hvotes Hin Hscope
  obtain ⟨Hperm, H0, Hcl, Hcvo, Hcln, Hcal, Hidx61⟩ := Hscope
  wp_start as H
  iNamed H
  wp_auto
  -- `s.Metadata.Index <= r.raftLog.committed`
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
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
    iframe Hphys
    ipureintro
    exact .inl ⟨Hst, rfl, rfl⟩
  rw [decide_eq_false Hst]
  wp_auto
  -- `r.state != StateFollower`: a follower
  wp_apply raft.wp_load_state $$ Hphys as Hphys
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
  -- the outer loop runs once: `id` is among the voters, so the inner loop breaks with
  -- `found`, and so does the outer one
  ihave IH : (∃ (k : w64) (st : GoSlice),
      "i" ∷ i_ptr ↦ k ∗ "set" ∷ set_ptr ↦ st ∗ "found" ∷ found_ptr ↦ false ∗
      "%Hk" ∷ ⌜k = W64 0⌝) $$ [i set found]
  · iexists W64 0, zero_val GoSlice
    iframe i set found
    ipureintro; rfl
  wp_for IH
  subst Hk
  wp_if_destruct
  rotate_left
  · exfalso; apply Hif; word
  wp_apply wp_load_slice_index (V := GoSlice) (t := go.uint64.SliceType) _ (sint.Z (W64 0)) _ _
      sv.Metadata'.ConfState'.Voters' (by decide) $$ [$Hrsl] as Hrsl
  · ipureintro; rfl
  ihave %Hvlen := ownSlice_len $$ Hvoters
  have Hidv : id ∈ voters := by
    have := (GMap.elem_of_elements cfg id).2 Hin
    exact Hperm.mem_iff.2 this
  ihave IH2 : (∃ (k2 x : w64),
      "i" ∷ i_ptr ↦ k2 ∗ "id" ∷ id_ptr ↦ x ∗ "found" ∷ found_ptr ↦ false ∗
      "%Hk2" ∷ ⌜(0 ≤ sint.Z k2 ∧ sint.Z k2 ≤ (voters.length : Int)) ∧
                id ∉ voters.take (sint.Z k2).toNat⌝) $$ [i id found]
  · iexists W64 0, zero_val w64
    iframe i id found
    ipureintro
    exact ⟨⟨by word, by word⟩, by simp⟩
  wp_for IH2
  obtain ⟨Hk2b, Hk2n⟩ := Hk2
  wp_if_destruct
  rotate_left
  · -- the voters ran out without `id`: impossible
    exfalso; apply Hk2n
    rw [List.take_of_length_le (by word)]; exact Hidv
  list_elem voters (sint.Z k2).toNat as y
  rw [ite_eq_left (show 0 ≤ sint.Z k2 ∧ sint.Z k2 < sint.Z sv.Metadata'.ConfState'.Voters'.len
    by word)]
  wp_apply wp_load_slice_index (V := w64) (t := go.uint64) _ (sint.Z k2) voters _ y
      (by omega) $$ [$Hvoters] as -
  · ipureintro; exact Hy_lookup
  wp_apply raft.wp_load_id $$ Hphys as Hphys
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
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
  wp_apply wp_raftLog_matchTerm _ _ { term' := sv.Metadata'.Term', index' := sv.Metadata'.Index' }
    $$ [$Hlog] as %b ⟨Hlog, %Hb⟩
  ihave Hphys := Hlogback $$ Hlog
  change b = decide (PlogMatches _ _ (snapId sv)) at Hb
  by_cases Hm : PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (snapId sv)
  · -- the log has the snapshot's last entry: fast-forward the commit
    rw [Hb, decide_eq_true Hm]
    wp_auto
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_apply wp_raftLog_lastEntryID $$ [$Hlog] as %last ⟨Hlog, -⟩
    ihave Hphys := Hlogback $$ Hlog
    -- the `Infof`: `r.id`, `r.raftLog.committed`, the two ids
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv2, Hl, -, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    wp_raft_log
    -- `commitTo(Index)`: in range, the log has a term at `Index`
    obtain ⟨-, Hle⟩ := plogTermAt_some_range _ _ _ _ Hm
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_at $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_apply wp_raftLog_commitTo _ _ sv.Metadata'.Index' Hle $$ [$Hlog] as Hlog
    ihave Hphys := Hlogback $$ Hlog
    iapply HΦ $$ %false %_
    iframe Hphys
    ipureintro
    refine .inr (.inl ⟨by simp only [snapId]; omega, Hm, rfl, ?_⟩)
    simp only [plogCommitTo, snapId] at *
    rw [ite_eq_left (by omega)]
  · rw [Hb, decide_eq_false Hm]
    wp_auto
    -- `r.raftLog.restore(s)`
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_at $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_apply wp_raftLog_restore _ _ sv voters (by simp only [snapId]; omega)
        (by simp only [snapId]; omega) $$ [$Hlog $Hvoters] as Hlog
    ihave Hphys := Hlogback $$ %_ Hlog
    -- the tracker replaced by the empty one, the log used meanwhile
    icases ownRaftPhys_retrack _ ∅ $$ Hphys with ⟨%tv, Htrkf, Htrk, Hlf, Hlog, Hback⟩
    icases ownTracker_maxinflight $$ Htrk with ⟨%Hmi, -⟩
    wp_auto
    wp_apply wp_MakeProgressTracker as %tv0 %v0 ⟨%Htv0, Hv0, Hvotes0, Hprs0⟩
    obtain ⟨Htv0mi, Htv0mb, Htv0arr, Htv0l, Htv0ln, Htv0al⟩ := Htv0
    wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, -⟩
    -- `confchange.Restore`: the empty tracker, the voters-only `ConfState`
    ipersist Hprs0
    have Hmi0 : 0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62 := by
      rw [Htv0mi]; exact Hmi
    have Hvne : voters ≠ [] := by rintro rfl; simp at Hidv
    have Hv0n : W64 0 ∉ voters := fun h =>
      H0 ((GMap.elem_of_elements cfg _).1 (Hperm.mem_iff.1 h))
    wp_apply wp_confchange_Restore { Tracker' := tv0, LastIndex' := li } _ voters DFrac.discard v0
        Hvne Hv0n Hcvo Hcl Hcln Hmi0 Htv0arr Htv0l Htv0ln $$ [$Hvoters $Hv0 $Hprs0]
      as %cfgv %prsm %prs %vref %vm ⟨-, Hv0, -, %Hcfgv, Hvref, %Hvm, Hprsm, %Hprs, Hprogs⟩
    obtain ⟨Hcfgarr, Hcfgl, Hcfgln, Hcfgal⟩ := Hcfgv
    -- the struct, re-sealed over the empty configuration
    ihave Htrk0 := ownTracker_empty tv0 v0 Htv0arr Htv0l Htv0ln Htv0al Hmi0 $$ Hv0 Hvotes0 Hprs0
    ihave Hphys := Hback $$ %tv0 %∅ %∅ %∅ %_ Hlf Htrkf Htrk0 Hlog
    -- `assertConfStatesEquivalent(r.logger, cs, r.switchToConfig(cfg, trk))`
    wp_apply raft.wp_load_logger $$ Hphys as %lok0 ⟨Hphys, #Hlg0⟩
    have Hcfgeq : GMap.listToSet voters = cfg := by
      apply GMap.set_eq; intro x
      rw [GMap.elem_of_list_to_set, Hperm.mem_iff, GMap.elem_of_elements]
    have Hcsz : (GMap.size cfg : Int) < 2 ^ 63 := by
      rw [← GMap.length_elements, ← Hperm.length_eq, Hvlen.1]; word
    ipersist Hprsm
    ihave Hcfg : ownConfig cfg cfgv prsm prs $$ [Hvref Hprogs]
    · unfold ownConfig
      iexists vref, vm
      simp only [named]
      iframe Hvref Hprsm Hprogs
      ipureintro
      rw [← Hcfgeq]
      exact ⟨Hcfgarr, Hcfgl, Hcfgln, Hcfgal, Hvm, Hprs, Hcfgeq ▸ Hcsz⟩
    wp_apply wp_raft_switchToConfig _ _ _ _ _ cfgv prsm prs (by simp [Hrole]) $$ [$Hphys $Hcfg]
      as %cs2 %xs2 %pvs1 ⟨Hphys, Hcs2v, %Hxs2, %Hcs2l⟩
    obtain ⟨Hc2a, Hc2b, Hc2c, Hc2al⟩ := Hcs2l
    have Hperm2 : voters ≡ₚ xs2 := Hperm.trans Hxs2.symm
    wp_apply wp_assertConfStatesEquivalent _ _ cs2 voters xs2 DFrac.discard (DFrac.own 1)
        Hperm2 Hcvo Hcl Hcln Hc2a Hc2b Hc2c (by rw [Hcal, Hc2al]) $$ [$Hvoters $Hcs2v] as -
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_apply wp_raftLog_lastEntryID $$ [$Hlog] as %last ⟨Hlog, -⟩
    ihave Hphys := Hlogback $$ Hlog
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv3, Hl, -, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    wp_raft_log
    iapply HΦ $$ %true %_
    iframe Hphys
    ipureintro
    refine .inr (.inr ⟨by simp only [snapId]; omega, Hm, rfl, prs, pvs1, ?_⟩)
    obtain ⟨⟩ := s
    simp only at Hvotes
    subst Hvotes
    rfl

end proof

end EtcdGrove
end Perennial
