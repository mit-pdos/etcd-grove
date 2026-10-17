/-
Port of election_proof/proof_raftLog__maybeAppend.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__maybeAppend
public import Proof.go_etcd_io.raft.v3.LemmasRaftlogW
public import Spec.go_etcd_io.raft.v3.raftLog__findConflict
public import Spec.go_etcd_io.raft.v3.raftLog__append
public import Spec.go_etcd_io.raft.v3.raftLog__commitTo
public import Spec.go_etcd_io.raft.v3.logSlice__lastIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [FfiSyntax]

/-- `logTruncateAppend` moves only the entry lists. -/
private theorem logTruncateAppend_fields (ls : LogState) (ents : List EntryM) :
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
private theorem matches_le_last (b : entryID) (es : List EntryM) (id : entryID) :
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
  · rw [show w64Min a b = a from ite_eq_left Hif]
    iapply HΦ; itrivial
  · rw [show w64Min a b = b from ite_eq_right Hif]
    iapply HΦ; itrivial

end proof0

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The suffix of an entry slice from `k` on (`s[k:]`). -/
private theorem entsPts_drop (k : w64) (s : GoSlice) (dq : DFrac) (es : List EntryM)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s.len) :
    entsPts (GF := GF) s dq es ⊢ entsPts (slice.slice s Loc k s.len) dq (es.drop (sint.nat k)) := by
  iintro H
  iunfold entsPts at H
  icases H with ⟨%lps, Hs, #Hb⟩
  icases (ownSlice_split_all k s dq lps hk).1 $$ Hs with ⟨-, Hs⟩
  iunfold entsPts
  iexists lps.drop (sint.nat k)
  iframe Hs
  iapply entsBig_drop
  iexact Hb

/-- etcd-io/raft#155: `findConflict` now does the `prev` check and returns the last match
`m`; the batch is fast-forwarded to `a.entries[m.index-a.prev.index:]` and always handed to
`append` (empty when the log has every entry, where `append` returns at once). The removed
`Panicf` (`ci <= l.committed`) is `append`'s, which the conflict premise kills the same way:
the first entry left is the old conflict index (`plogFindMatch_drop`). -/
theorem raftLog.maybeAppend.wp_proof
    (wp_raftLog_findConflict : raftLog.findConflict.spec (GF := GF) (hG := hG))
    (wp_raftLog_append : raftLog.append.spec (GF := GF) (hG := hG))
    (wp_raftLog_commitTo : raftLog.commitTo.spec (GF := GF) (hG := hG))
    (wp_logSlice_lastIndex : logSlice.lastIndex.spec (GF := GF) (hG := hG)) :
    raftLog.maybeAppend.spec (GF := GF) (hG := hG) := by
  intro l ls a ents committed Hwf Hnw Hci
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := entsPts_len _ _ _ $$ Hents
  icases ownRaftLog_wf _ _ $$ Hlog with ⟨%Hidx, Hlog⟩
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hcmb, Hlog⟩
  icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hnwl, Hlog⟩
  wp_apply wp_raftLog_findConflict _ ls a _ ents Hwf $$ [$Hlog $Hents]
    as %m %ok ⟨Hlog, -, %Hfc⟩
  obtain ⟨Hok, Hmeq, -⟩ := Hfc
  cases ok with
  | false =>
    -- `a.prev` does not match: `(0, false)`
    have Hnm : ¬ PlogMatches ls.prev (ls.sents ++ ls.uents) a.prev' := of_decide_eq_false Hok.symm
    wp_auto
    iapply HΦ
    iframe
    isplitr
    · ipureintro
      simp [plogMaybeAppend, Hnm]
    ipureintro; exact ⟨rfl, id⟩
  | true =>
    have Hpm : PlogMatches ls.prev (ls.sents ++ ls.uents) a.prev' := of_decide_eq_true Hok.symm
    have Hm := Hmeq rfl
    obtain ⟨k, Hkle, Hmidx, Hmm, -, Hd⟩ :=
      plogFindMatch_drop ls.prev (ls.sents ++ ls.uents) a.prev' ents Hwf
    rw [← Hm] at Hmidx Hmm
    have Hmin := matches_le_last _ _ _ (Hmm Hpm)
    simp only [plogLastIndexZ, List.length_append] at Hmin
    simp only [plogMaybeAppend, ite_eq_left Hpm]
    have Hci := Hci Hpm
    wp_auto
    have Hsub : m.index' - a.prev'.index' = W64 (k : Int) := by word
    rw [Hsub]
    -- the batch from the first entry the log does not have: `a.entries[k:]`
    ihave #Hdrop := entsPts_drop (W64 (k : Int)) a.entries' DFrac.discard ents (by word) $$ Hents
    ihave %Hcapwf := ownSliceCap_wf _ _ $$ Hcap
    icases (ownSliceCap_slice a.entries' (W64 (k : Int)) (DFrac.own 1) (by word)).1 $$ Hcap
      with Hcap'
    have Hkn : sint.nat (W64 (k : Int)) = k := by word
    rw [Hkn]
    ihave Hadopt : (if logAdopts ls (ents.drop k)
        then iprop(⌜DFrac.discard = DFrac.discard⌝ ∗
          ownSliceCap Loc (slice.slice a.entries' Loc (W64 (k : Int)) a.entries'.len)
            (DFrac.own 1))
        else iprop(True)) $$ [Hcap']
    · split
      · iframe; ipureintro; rfl
      · itrivial
    have Hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) ≤ sint.Z a.entries'.len ∧
        sint.Z a.entries'.len ≤ sint.Z a.entries'.cap := by
      word
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hbnd)]
    wp_auto
    -- `append`'s premises: the first entry left is the old conflict index, above `committed`
    -- (the conflict premise), and right after `m`, which the log has
    have Happ_pre : ∀ e0, (ents.drop k)[0]? = some e0 →
        (uint.Z ls.committed < uint.Z e0.Index' ∧
          uint.Z e0.Index' ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
            + (ls.uents.length : Int) + 1) ∧
        (∀ (j : Nat) e', (ents.drop k)[j]? = some e' →
          uint.Z e'.Index' = uint.Z e0.Index' + (j : Int)) ∧
        uint.Z e0.Index' + ((ents.drop k).length : Int) < 2^64 := by
      intro e0 He0
      have He0' : ents[k]? = some e0 := by simpa [List.getElem?_drop] using He0
      have Hke := Hwf k e0 He0'
      have Hcie : plogFindConflict ls.prev (ls.sents ++ ls.uents) ents = e0.Index' := by
        have Hdk : ents.drop k = e0 :: ents.drop (k + 1) := by
          rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 He0').1]
          rw [(List.getElem?_eq_some_iff.1 He0').2]
        rw [Hdk] at Hd
        exact Hd.1
      have Hcine : e0.Index' ≠ W64 0 := by intro Hc; rw [Hc] at Hke; word
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rcases Hci with Hc | Hc
        · exact absurd (Hcie ▸ Hc) Hcine
        · rwa [Hcie] at Hc
      · push_cast at Hke; omega
      · intro j ej Hj
        rw [List.getElem?_drop] at Hj
        have := Hwf _ _ Hj
        push_cast at *
        omega
      · rw [List.length_drop]
        push_cast at Hke
        omega
    icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hrw, Hlog⟩
    have Hnu : nextUnstable ls ≠ [] →
        nextUnstable (logTruncateAppend ls (ents.drop k)) ≠ [] := by
      intro Hne
      cases Hdk : ents.drop k with
      | nil => exact Hne
      | cons e rest =>
        have He2 : (ents.drop k)[0]? = some e := by rw [Hdk]; rfl
        obtain ⟨⟨Hgt, Hle⟩, -, -⟩ := Happ_pre e He2
        rw [← Hdk]
        exact nextUnstable_truncateAppend_ne ls (ents.drop k) e He2 Hrw.1.1 Hrw.1.2
          (by omega) Hle
    wp_apply wp_raftLog_append _ ls (ents.drop k) _ _
        Happ_pre $$ [$Hlog $Hdrop $Hadopt]
      as %li ⟨Hlog, -, %Hsplit, %Hli⟩
    obtain ⟨Hp1, Hc1, Ha1, Hag1, Hsn1, Hun1, Hst1, Hsg1⟩ := logTruncateAppend_fields ls
      (ents.drop k)
    -- the new entries are the old spec's: unchanged if the log had them all, else
    -- `truncateAndAppend` from the old conflict index on
    have Hes' : plogTruncateAppend ls.prev (ls.sents ++ ls.uents) (ents.drop k) =
        (if plogFindConflict ls.prev (ls.sents ++ ls.uents) ents = W64 0
         then ls.sents ++ ls.uents
         else plogTruncateAppend ls.prev (ls.sents ++ ls.uents)
           (ents.drop (uint.Z (plogFindConflict ls.prev (ls.sents ++ ls.uents) ents)
              - uint.Z a.prev'.index' - 1).toNat)) := by
      cases Hdk : ents.drop k with
      | nil =>
        rw [Hdk] at Hd
        rw [Hd]; rfl
      | cons e rest =>
        rw [Hdk] at Hd
        have He0' : ents[k]? = some e := by
          have : (ents.drop k)[0]? = some e := by rw [Hdk]; rfl
          simpa [List.getElem?_drop] using this
        have Hke := Hwf k e He0'
        have Hcine : e.Index' ≠ W64 0 := by intro Hc; rw [Hc] at Hke; word
        rw [Hd.1, ite_eq_right Hcine]
        have Hkd : (uint.Z e.Index' - uint.Z a.prev'.index' - 1).toNat = k := by
          push_cast at Hke; omega
        rw [Hkd, Hdk]
    generalize Hls1 : logTruncateAppend ls (ents.drop k) = ls1
      at Hsplit Hli Hp1 Hc1 Ha1 Hag1 Hsn1 Hun1 Hst1 Hsg1 Hnu ⊢
    -- the new log reaches `lastnewi` (exactly, unless the log already had every entry)
    have Hlast1 : uint.Z a.prev'.index' + (ents.length : Int) ≤
        uint.Z ls.prev.index' + (ls1.sents.length : Int) + (ls1.uents.length : Int) := by
      have HL := congrArg List.length Hsplit
      simp only [List.length_append] at HL
      cases Hdk : ents.drop k with
      | nil =>
        rw [Hdk] at HL
        have : ents.length ≤ k := List.drop_eq_nil_iff.1 Hdk
        simp only [plogTruncateAppend, List.length_append] at HL
        have := Hmin.2
        omega
      | cons e rest =>
        rw [Hdk] at HL
        have He0' : ents[k]? = some e := by
          have : (ents.drop k)[0]? = some e := by rw [Hdk]; rfl
          simpa [List.getElem?_drop] using this
        have Hke := Hwf k e He0'
        push_cast at Hke
        have Hlr : rest.length = ents.length - k - 1 := by
          have := congrArg List.length Hdk
          simp only [List.length_drop, List.length_cons] at this
          omega
        obtain ⟨⟨Hgt, Hle⟩, -, -⟩ := Happ_pre e (by rw [Hdk]; rfl)
        simp only [plogTruncateAppend, List.length_append, List.length_take,
          List.length_cons] at HL
        omega
    -- `a.lastIndex()` on the pointer: load the slice, call the value method
    wp_method_call
    wp_auto
    wp_apply wp_logSlice_lastIndex
    have Hlni : m.index' + (a.entries'.len - W64 (k : Int))
        = W64 (uint.Z a.prev'.index' + (ents.length : Int)) := by
      word
    rw [Hlni]
    wp_apply wp_min_u64
    wp_apply wp_raftLog_commitTo _ ls1 _ ?_ $$ [$Hlog] as Hlog
    · rw [Hp1]
      simp only [plogLastIndexZ, List.length_append, w64Min]
      split <;> word
    wp_method_call
    wp_auto
    wp_apply wp_logSlice_lastIndex
    rw [Hlni]
    iapply HΦ
    iframe
    isplitr
    · ipureintro
      simp only [w64Min, true_and]
      exact ⟨Hp1, by rw [Hsplit, Hes'], Ha1, by rw [Hc1], Hag1, Hsn1, Hun1, Hst1, Hsg1⟩
    ipureintro; exact ⟨Hsn1, Hnu⟩

end proof

end EtcdGrove
end Perennial
