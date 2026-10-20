/-
Proof of `Spec/go_etcd_io/raft/v3/raftLog__subterm.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__subterm
public import Spec.go_etcd_io.raft.v3.raftLog__firstIndex
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raftLog__slice
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetSubterm
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage

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

theorem raftLog.subterm.wp_proof
    (wp_raftLog_firstIndex : raftLog.firstIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_slice : raftLog.slice.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetSubterm : raftpb.Entry.GetSubterm.spec (GF := GF) (hG := hG)) :
    raftLog.subterm.spec (GF := GF) (hG := hG) := by
  intro l ls i
  wp_start as Hlog
  iNamed Hlog
  wp_auto
  icases ownRaftLog_nowrap l ls $$ Hlog with ⟨%Hnw, Hlog⟩
  wp_apply wp_raftLog_firstIndex l ls $$ [$Hlog] as %fi ⟨Hlog, %Hfi, -⟩
  by_cases Hlo : uint.Z i < uint.Z fi
  · -- before the first index: none
    rw [decide_eq_true Hlo]
    wp_auto
    iapply HΦ
    iframe Hlog
    isplitr
    · ipureintro; intro h; cases h
    · ipureintro; intro _; rfl
  rw [decide_eq_false Hlo]
  wp_auto
  wp_apply wp_raftLog_lastIndex l ls $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
  by_cases Hhi : uint.Z li < uint.Z i
  · -- past the last index: none
    rw [decide_eq_true Hhi]
    wp_auto
    iapply HΦ
    iframe Hlog
    isplitr
    · ipureintro; intro h; cases h
    · ipureintro; intro _; rfl
  rw [decide_eq_false Hhi]
  wp_auto
  wp_apply wp_raftLog_slice l ls i (i + W64 1) _ (by word) $$ [$Hlog] as %sl %es %err ⟨Hlog, Hr⟩
  icases Hr with (⟨%Herr, #Hs, %Hes, -⟩ | ⟨⟨%Hsl, -⟩, #Hc, -⟩)
  rotate_left
  · -- compacted: `ErrCompacted`, none
    ihave #Hinit := isInitialized_access $$ Hpkg
    iNamed Hinit
    icombine Hc ErrCompacted gives %Heq
    subst Heq
    obtain ⟨ty, p, rfl⟩ := HErrCompacted_new
    wp_auto
    iapply HΦ
    iframe Hlog
    isplitr
    · ipureintro; intro h; cases h
    · ipureintro; intro _; rfl
  subst Herr
  obtain ⟨Hne, -, -, Hpre⟩ := Hes
  obtain ⟨e, es', rfl⟩ : ∃ e es', es = e :: es' := by
    cases es with
    | nil => exact absurd rfl Hne
    | cons e es' => exact ⟨e, es', rfl⟩
  have Hlk : (e :: es')[0]? = some e := rfl
  icases entsRO_lookup sl (e :: es') 0 e Hlk $$ Hs with ⟨%lsl, %le, #Hsl, #He, %Hlen⟩
  obtain ⟨Hl0, -, Hlen2, Hlen3⟩ := Hlen
  have Hslz : sl.len ≠ W64 0 := by
    intro h
    rw [h] at Hlen2
    simp only [List.length_cons] at Hlen2
    have : sint.nat (W64 0) = 0 := by word
    omega
  wp_auto
  rw [decide_eq_false Hslz]
  wp_auto
  rw [ite_eq_left ⟨by word, by simp at Hlen2; word⟩]
  wp_apply wp_load_slice_index (V := Loc) sl (sint.Z (W64 0)) lsl DFrac.discard le (by word) $$ [Hsl]
    with -
  · iframe Hsl; ipureintro; simpa using Hl0
  wp_apply wp_GetTerm.1 le DFrac.discard e $$ [He] with -
  · iframe He
  rw [ite_eq_left ⟨by word, by simp at Hlen2; word⟩]
  wp_apply wp_load_slice_index (V := Loc) sl (sint.Z (W64 0)) lsl DFrac.discard le (by word) $$ [Hsl]
    with -
  · iframe Hsl; ipureintro; simpa using Hl0
  wp_apply wp_GetSubterm.1 le DFrac.discard e $$ [He] with -
  · iframe He
  iapply HΦ
  iframe Hlog
  isplitr
  · ipureintro
    intro _
    have Hi1 : uint.Z ls.prev.index' < uint.Z i := by omega
    refine ⟨Hi1, e, ?_, rfl, rfl⟩
    obtain ⟨r, Hr⟩ := Hpre
    unfold plogFrom at Hr
    have := congrArg (fun l => l[0]?) Hr
    simp only [List.cons_append, List.getElem?_cons_zero, List.getElem?_drop, Nat.add_zero] at this
    exact this.symm
  · ipureintro; intro h; cases h

end proof

end EtcdGrove
end Perennial
