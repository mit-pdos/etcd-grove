/-
Proof of `(*raftLog).subterm` (`log.go:314`, witness support). Lean-first (2026-10-20).
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__subterm
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__firstIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__slice
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetSubterm
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Three exits: out of `[firstIndex, lastIndex]` (`false`); `slice(i, i+1)` failing with
`ErrCompacted` (`false`; its result is the nil slice, so the `len(ents) == 0` test is moot);
and the slice's first entry, which is the log's entry at `i` (`slice`'s `plogFrom` prefix). -/
theorem raftLog.subterm.wp_proof
    (wp_raftLog_firstIndex : raftLog.firstIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_slice : raftLog.slice.spec (GF := GF) (hG := hG))
    (wp_Entry_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (wp_Entry_GetSubterm : raftpb.Entry.GetSubterm.spec (GF := GF) (hG := hG)) :
    raftLog.subterm.spec (GF := GF) (hG := hG) := by
  intro l ls i
  wp_start as H
  iNamed H
  wp_auto
  icases ownRaftLog_nowrap l ls $$ Hlog with ⟨%Hnw, Hlog⟩
  wp_apply wp_raftLog_firstIndex _ ls $$ [$Hlog] as %fi ⟨Hlog, %Hfi, -⟩
  by_cases Hb1 : uint.Z i < uint.Z fi
  · rw [decide_eq_true Hb1]
    wp_auto
    iapply HΦ
    iframe Hlog
    ipureintro; intro Hc; cases Hc
  rw [decide_eq_false Hb1]
  wp_auto
  wp_apply wp_raftLog_lastIndex _ ls $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
  by_cases Hb2 : uint.Z li < uint.Z i
  · rw [decide_eq_true Hb2]
    wp_auto
    iapply HΦ
    iframe Hlog
    ipureintro; intro Hc; cases Hc
  rw [decide_eq_false Hb2]
  wp_auto
  have Hi1 : uint.Z (i + W64 1) = uint.Z i + 1 := by word
  have Hsl : uint.Z ls.prev.index' + 1 ≤ uint.Z i ∧ uint.Z i < uint.Z (i + W64 1) ∧
      uint.Z (i + W64 1) ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
        + (ls.uents.length : Int) + 1 := by omega
  wp_apply wp_raftLog_slice l ls _ _ _ Hsl $$ [$Hlog] as %s %es %err ⟨Hlog, Hr⟩
  icases Hr with (⟨%Herr, #Hes, ⟨%Hne, %Hlen, %_, %Hpre⟩, -⟩ | ⟨⟨%Hs, %_⟩, -, -⟩)
  · subst Herr
    wp_auto
    ihave %Hslen := entsPts_len $$ Hes
    obtain ⟨e, es', rfl⟩ : ∃ e es', es = e :: es' := by
      cases es with
      | nil => exact absurd rfl Hne
      | cons e es' => exact ⟨e, es', rfl⟩
    have Hsne : s.len ≠ W64 0 := by
      intro Heq0; rw [Heq0] at Hslen
      exact absurd Hslen.1 (by rw [show sint.nat (W64 0) = 0 by rfl]; simp)
    simp only [Hsne, decide_false]
    wp_auto
    icases entsRO_lookup s (e :: es') 0 e rfl $$ Hes with ⟨%ls1, %l1, #Hls1, #He1, %Hl1⟩
    have H0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len := by
      obtain ⟨-, Hl, Hz⟩ := Hl1.2
      simp only [List.length_cons] at Hl
      constructor <;> word
    simp only [H0, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z (W64 0)) ls1 DFrac.discard l1 (by word) $$ [Hls1] with -
    · iframe Hls1; ipureintro; exact Hl1.1
    wp_apply wp_Entry_GetTerm.1 l1 DFrac.discard e $$ [He1] with -
    · iframe He1
    simp only [H0, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z (W64 0)) ls1 DFrac.discard l1 (by word) $$ [Hls1] with -
    · iframe Hls1; ipureintro; exact Hl1.1
    wp_apply wp_Entry_GetSubterm.1 l1 DFrac.discard e $$ [He1] with -
    · iframe He1
    iapply HΦ
    iframe Hlog
    ipureintro
    intro _
    refine ⟨e, ?_, rfl, rfl⟩
    rw [plogEntryAt_lookup _ _ _ (by omega)]
    obtain ⟨t, Ht⟩ := Hpre
    unfold plogFrom at Ht
    have H := congrArg (fun xs : List EntryM => xs[0]?) Ht
    simp only [List.cons_append, List.getElem?_cons_zero, List.getElem?_drop,
      Nat.add_zero] at H
    exact H.symm
  · subst Hs
    cases err <;> wp_auto
    all_goals
      iapply HΦ
      iframe Hlog
      ipureintro; intro Hc; cases Hc

end proof

end EtcdGrove
end Perennial
