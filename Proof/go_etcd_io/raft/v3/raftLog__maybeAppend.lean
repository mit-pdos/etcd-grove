/-
Port of election_proof/proof_raftLog__maybeAppend.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__maybeAppend
public import Spec.go_etcd_io.raft.v3.raftLog__matchTerm
public import Spec.go_etcd_io.raft.v3.raftLog__findConflict
public import Spec.go_etcd_io.raft.v3.raftLog__append
public import Spec.go_etcd_io.raft.v3.raftLog__commitTo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [FfiSyntax]

/-- Pure facts about `plogFindConflict` the proof needs: it is `0` exactly when every
entry matches (for a batch with no index `0`), and otherwise it is the index of the
first entry that does not. -/
private theorem find_conflict_cases (b : entryID) (es ents : List raftpb.Entry) :
    (plogFindConflict b es ents = W64 0 ∧ ∀ e ∈ ents, PlogMatches b es (entId e)) ∨
    (∃ (k : Nat) (e : raftpb.Entry), ents[k]? = some e ∧
      plogFindConflict b es ents = e.Index' ∧
      ¬ PlogMatches b es (entId e) ∧
      ∀ (j : Nat) e', j < k → ents[j]? = some e' → PlogMatches b es (entId e')) := by
  induction ents with
  | nil => exact .inl ⟨rfl, by simp⟩
  | cons e ents IH =>
    by_cases Hm : PlogMatches b es (entId e)
    · rcases IH with ⟨H0, Hall⟩ | ⟨k, e', Hk, Hci, Hnm, Hbefore⟩
      · refine .inl ⟨?_, ?_⟩
        · simp only [plogFindConflict, if_pos Hm]; exact H0
        · intro x Hx
          rcases List.mem_cons.1 Hx with rfl | Hx
          · exact Hm
          · exact Hall x Hx
      · refine .inr ⟨k + 1, e', by simpa using Hk, ?_, Hnm, ?_⟩
        · simp only [plogFindConflict, if_pos Hm]; exact Hci
        · intro j e'' Hj Hj'
          cases j with
          | zero => simp at Hj'; subst Hj'; exact Hm
          | succ j => exact Hbefore j e'' (by omega) (by simpa using Hj')
    · refine .inr ⟨0, e, rfl, ?_, Hm, fun j _ Hj _ => absurd Hj (Nat.not_lt_zero _)⟩
      simp only [plogFindConflict, if_neg Hm]

/-- `logTruncateAppend` moves only the entry lists. -/
private theorem logTruncateAppend_fields (ls : LogState) (ents : List raftpb.Entry) :
    (logTruncateAppend ls ents).prev = ls.prev ∧
    (logTruncateAppend ls ents).committed = ls.committed ∧
    (logTruncateAppend ls ents).applied = ls.applied ∧
    (logTruncateAppend ls ents).applying = ls.applying ∧
    (logTruncateAppend ls ents).snap = ls.snap ∧
    (logTruncateAppend ls ents).unpersisted = ls.unpersisted ∧
    (logTruncateAppend ls ents).stored = ls.stored ∧
    (logTruncateAppend ls ents).storage = ls.storage := by
  cases ents <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A matched entry is inside the log. -/
private theorem matches_le_last (b : entryID) (es : List raftpb.Entry) (id : entryID) :
    PlogMatches b es id →
    uint.Z b.index' ≤ uint.Z id.index' ∧ uint.Z id.index' ≤ plogLastIndexZ b es :=
  plogTermAt_some_range b es id.index' id.term'

end pure

section proof0
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]

/-- The builtin `min` on `uint64` (Rocq unfolds `minⁱᵐᵖˡ` in place). -/
private theorem wp_min_u64 (a b : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.min [go.uint64, go.uint64])) (Val #a)) (Val #b))
    {{ RET #(w64Min a b); True }} := by
  wp_start
  wp_if_destruct
  · rw [show w64Min a b = a from if_pos Hif]
    iapply HΦ; itrivial
  · rw [show w64Min a b = b from if_neg Hif]
    iapply HΦ; itrivial

end proof0

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftLog.maybeAppend.wp_proof
    (wp_raftLog_matchTerm : raftLog.matchTerm.spec (GF := GF) (hG := hG))
    (wp_raftLog_findConflict : raftLog.findConflict.spec (GF := GF) (hG := hG))
    (wp_raftLog_append : raftLog.append.spec (GF := GF) (hG := hG))
    (wp_raftLog_commitTo : raftLog.commitTo.spec (GF := GF) (hG := hG)) :
    raftLog.maybeAppend.spec (GF := GF) (hG := hG) := by
  intro l ls a ents committed Hwf Hnw Hci
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hents
  icases ownRaftLog_wf _ _ $$ Hlog with ⟨%Hidx, Hlog⟩
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hcmb, Hlog⟩
  icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hnwl, Hlog⟩
  wp_apply wp_raftLog_matchTerm _ ls a.prev' $$ [$Hlog]
    as %b ⟨Hlog, %Hb⟩
  cases b with
  | false =>
    -- `a.prev` does not match: `(0, false)`
    have Hnm : ¬ PlogMatches ls.prev (ls.sents ++ ls.uents) a.prev' := of_decide_eq_false Hb.symm
    wp_auto
    iapply HΦ
    iframe
    isplitr
    · ipureintro
      simp [plogMaybeAppend, Hnm]
    ipureintro; exact ⟨rfl, id⟩
  | true =>
    have Hm : PlogMatches ls.prev (ls.sents ++ ls.uents) a.prev' := of_decide_eq_true Hb.symm
    simp only [plogMaybeAppend, if_pos Hm]
    have Hci := Hci Hm
    have Hprange := matches_le_last _ _ _ Hm
    simp only [plogLastIndexZ, List.length_append] at Hprange
    wp_auto
    -- `findConflict`: every entry is above `a.prev`, hence above `ls.prev`
    have Hge : ∀ e ∈ ents, uint.Z ls.prev.index' ≤ uint.Z e.Index' := by
      intro e He
      obtain ⟨k, Hk⟩ := List.getElem?_of_mem He
      have := Hwf k e Hk
      omega
    wp_apply wp_raftLog_findConflict _ ls _ _ ents Hge
      $$ [$Hlog $Hents] as ⟨Hlog, -⟩
    have Hlni : a.prev'.index' + a.entries'.len = W64 (uint.Z a.prev'.index' + (ents.length : Int)) := by
      word
    rw [Hlni]
    rcases find_conflict_cases ls.prev (ls.sents ++ ls.uents) ents with
      ⟨Hci0, Hall⟩ | ⟨k, e, Hk, Hcie, Hnm, Hbefore⟩
    · -- no conflict: the log already has every entry
      rw [Hci0]
      wp_auto
      -- the log reaches `lastnewi`
      have Hreach : uint.Z a.prev'.index' + (ents.length : Int)
          ≤ uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int) := by
        cases Hl : ents.getLast? with
        | none =>
          rw [List.getLast?_eq_none_iff] at Hl
          subst Hl
          simp only [List.length_nil]
          omega
        | some el =>
          have Hel := getLast?_some_getElem? ents el Hl
          have Hm' := matches_le_last _ _ _ (Hall el (List.mem_of_getLast? Hl))
          simp only [plogLastIndexZ, List.length_append, entId] at Hm'
          have := Hwf _ _ Hel
          have Hne : ents ≠ [] := by intro h; subst h; simp at Hl
          have : 0 < ents.length := List.length_pos_iff.2 Hne
          rw [show ents.length - 1 + 1 = ents.length by omega] at *
          omega
      wp_apply wp_min_u64
      wp_apply wp_raftLog_commitTo _ ls _ ?_ $$ [$Hlog] as Hlog
      · simp only [plogLastIndexZ, List.length_append, w64Min]
        split <;> word
      iapply HΦ
      iframe
      isplitr
      · ipureintro
        simp only [w64Min, and_self, if_true]
      ipureintro; exact ⟨rfl, id⟩
    · -- a conflict at `ci = ents[k].Index = a.prev.index + 1 + k`
      have Hke := Hwf k e Hk
      have Hcine : e.Index' ≠ W64 0 := by intro Hc; rw [Hc] at Hke; word
      have Hcgt : uint.Z ls.committed < uint.Z e.Index' := by
        rcases Hci with Hc | Hc
        · exact absurd (Hcie ▸ Hc) Hcine
        · rwa [Hcie] at Hc
      rw [Hcie]
      have Hklt : k < ents.length := (List.getElem?_eq_some_iff.1 Hk).1
      simp only [Hcine, decide_false]
      wp_auto
      icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hback⟩
      obtain ⟨Hcm, -⟩ := Hlv
      wp_auto
      have Hnle : ¬ uint.Z e.Index' ≤ uint.Z lv.committed' := by rw [Hcm]; omega
      simp only [Hnle, decide_false]
      ihave Hlog := Hback $$ Hl
      wp_auto
      have Hsub : e.Index' - (a.prev'.index' + W64 1) = W64 (k : Int) := by word
      rw [Hsub]
      rw [decide_eq_false (by word)]
      wp_auto
      -- the batch from the conflict on: `a.entries[k:]`
      icases (ownSlice_split_all (W64 (k : Int)) a.entries' DFrac.discard ents (by word)).1 $$ Hents
        with ⟨-, #Hdrop⟩
      ihave %Hcapwf := ownSliceCap_wf _ _ $$ Hcap
      icases (ownSliceCap_slice a.entries' (W64 (k : Int)) (DFrac.own 1) (by word)).1 $$ Hcap
        with Hcap'
      have Hkn : sint.nat (W64 (k : Int)) = k := by word
      rw [Hkn]
      have He2 : (ents.drop k)[0]? = some e := by simpa using Hk
      ihave Hadopt : (if logAdopts ls (ents.drop k)
          then iprop(⌜DFrac.discard = DFrac.discard⌝ ∗
            ownSliceCap raftpb.Entry (slice.slice a.entries' raftpb.Entry (W64 (k : Int)) a.entries'.len)
              (DFrac.own 1))
          else iprop(True)) $$ [Hcap']
      · split
        · iframe; ipureintro; rfl
        · itrivial
      rw [Hsub]
      have Hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) ≤ sint.Z a.entries'.len ∧
          sint.Z a.entries'.len ≤ sint.Z a.entries'.cap := by
        word
      rw [ite_eq_left_of_eq_true _ _ (eq_true Hbnd)]
      wp_auto
      -- `ci <= lastIndex() + 1`: `ents[k-1]` (or `a.prev`) matched
      have Hcile : uint.Z e.Index' ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
          + (ls.uents.length : Int) + 1 := by
        cases k with
        | zero => omega
        | succ k' =>
          obtain ⟨e', He'⟩ : ∃ e', ents[k']? = some e' :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have Hm' := matches_le_last _ _ _ (Hbefore k' e' (by omega) He')
          simp only [plogLastIndexZ, List.length_append, entId] at Hm'
          have := Hwf k' e' He'
          push_cast at *
          omega
      have Happ_pre : ∀ e0, (ents.drop k)[0]? = some e0 →
          (uint.Z ls.committed < uint.Z e0.Index' ∧
            uint.Z e0.Index' ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
              + (ls.uents.length : Int) + 1) ∧
          (∀ (j : Nat) e', (ents.drop k)[j]? = some e' →
            uint.Z e'.Index' = uint.Z e0.Index' + (j : Int)) ∧
          uint.Z e0.Index' + ((ents.drop k).length : Int) < 2^64 := by
        intro e0 He0
        rw [He2] at He0
        cases He0
        refine ⟨⟨Hcgt, Hcile⟩, ?_, ?_⟩
        · intro j ej Hj
          rw [List.getElem?_drop] at Hj
          have := Hwf _ _ Hj
          push_cast at *
          omega
        · rw [List.length_drop]
          omega
      icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hrw, Hlog⟩
      have Hnu := nextUnstable_truncateAppend_ne ls (ents.drop k) e He2 Hrw.1.1 Hrw.1.2
        (by omega) Hcile
      wp_apply wp_raftLog_append _ ls (ents.drop k) _ _
          Happ_pre $$ [$Hlog $Hdrop $Hadopt]
        as %li ⟨Hlog, -, %Hsplit, %Hli⟩
      obtain ⟨Hp1, Hc1, Ha1, Hag1, Hsn1, Hun1, Hst1, Hsg1⟩ := logTruncateAppend_fields ls
        (ents.drop k)
      generalize Hls1 : logTruncateAppend ls (ents.drop k) = ls1
        at Hsplit Hli Hp1 Hc1 Ha1 Hag1 Hsn1 Hun1 Hst1 Hsg1 Hnu ⊢
      -- the new log reaches exactly `lastnewi`
      have Hdk : ents.drop k = e :: ents.drop (k + 1) := by
        rw [List.drop_eq_getElem_cons Hklt]
        rw [(List.getElem?_eq_some_iff.1 Hk).2]
      have Hlast1 : uint.Z ls.prev.index' + (ls1.sents.length : Int) + (ls1.uents.length : Int)
          = uint.Z a.prev'.index' + (ents.length : Int) := by
        have HL := congrArg List.length Hsplit
        rw [Hdk] at HL
        simp only [plogTruncateAppend, List.length_append, List.length_take,
          List.length_cons, List.length_drop] at HL
        push_cast at *
        omega
      wp_apply wp_min_u64
      wp_apply wp_raftLog_commitTo _ ls1 _ ?_ $$ [$Hlog] as Hlog
      · rw [Hp1]
        simp only [plogLastIndexZ, List.length_append, w64Min]
        push_cast
        split <;> word
      iapply HΦ
      iframe
      isplitr
      · ipureintro
        have Hkd : (uint.Z e.Index' - uint.Z a.prev'.index' - 1).toNat = k := by
          push_cast at Hke; omega
        simp only [Hkd, if_false, w64Min, true_and]
        exact ⟨Hp1, Hsplit, Ha1, by rw [Hc1], Hag1, Hsn1, Hun1, Hst1, Hsg1⟩
      ipureintro; exact ⟨Hsn1, fun _ => Hnu⟩

end proof

end EtcdGrove
end Perennial
