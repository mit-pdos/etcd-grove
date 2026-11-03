/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Storage__encode.lean`. Lean-first
(no Rocq counterpart): the image's fields read, each written with `putUint64`/`putSnapshot`, the
entries with `putEntry` in a loop over the image's (read-only) entry slice.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__encode
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.putUint64
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.putSnapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.putEntry
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetVote
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import Proof.go_etcd_io.raft.v3.LemmasEnts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

theorem encEntries_snoc [GooseExts] (l : List EntryM) (e : EntryM) :
    encEntries (l ++ [e]) = encEntries l ++ encEntry e := by
  induction l with
  | nil => simp [encEntries]
  | cons a r ih => simp [encEntries, ih, List.append_assoc]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- The getters of a hard state that may be `nil` (the zero one). -/
private theorem wp_hsOpt_get (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (p : Loc) (hs : HardStateM) :
    ({{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hsOpt p hs }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetTerm")) (Val #()))
    {{ RET #hs.Term'; True }}) ∧
    ({{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hsOpt p hs }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetVote")) (Val #()))
    {{ RET #hs.Vote'; True }}) ∧
    ({{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hsOpt p hs }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetCommit")) (Val #()))
    {{ RET #hs.Commit'; True }}) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · iintro %Φ ⟨#Hpkg, H⟩ HΦ
    iunfold hsOpt at H
    icases H with (%H | #H)
    · obtain ⟨rfl, rfl⟩ := H
      first
        | iapply wp_GetTerm.2 $$ [$Hpkg] [HΦ]
        | iapply wp_GetVote.2 $$ [$Hpkg] [HΦ]
        | iapply wp_GetCommit.2 $$ [$Hpkg] [HΦ]
      iexact HΦ
    · first
        | iapply wp_GetTerm.1 p hs $$ [$Hpkg $H] [HΦ]
        | iapply wp_GetVote.1 p hs $$ [$Hpkg $H] [HΦ]
        | iapply wp_GetCommit.1 p hs $$ [$Hpkg $H] [HΦ]
      iexact HΦ

theorem Storage.encode.wp_proof
    (wp_putUint64 : putUint64.spec (GF := GF) (hG := hG))
    (wp_putSnapshot : putSnapshot.spec (GF := GF) (hG := hG))
    (wp_putEntry : putEntry.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG)) :
    Storage.encode.spec (GF := GF) (hG := hG) := by
  intro s ip M
  wp_start as ⟨#Himg, HM⟩
  have Hhs := wp_hsOpt_get wp_GetTerm wp_GetVote wp_GetCommit
  iunfold ownImage at HM
  icases HM with ⟨%hsp, %sp, %es, HM⟩
  iNamed HM
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hnilc := ownSliceCap_nil (GF := GF) (V := w8)
  wp_apply (Hhs hsp M.hs).1 $$ [$Hpb $HhsO]
  wp_apply wp_putUint64 slice.nil [] M.hs.Term' $$ [$Hnil $Hnilc] as %b1 ⟨Hb, Hbc⟩
  wp_apply (Hhs hsp M.hs).2.1 $$ [$Hpb $HhsO]
  wp_apply wp_putUint64 b1 _ M.hs.Vote' $$ [$Hb $Hbc] as %b2 ⟨Hb, Hbc⟩
  wp_apply (Hhs hsp M.hs).2.2 $$ [$Hpb $HhsO]
  wp_apply wp_putUint64 b2 _ M.hs.Commit' $$ [$Hb $Hbc] as %b3 ⟨Hb, Hbc⟩
  wp_apply wp_putSnapshot b3 _ sp DFrac.discard M.snap $$ [$Hb $Hbc $HsnapO] as %b4 ⟨Hb, Hbc, -⟩
  wp_apply wp_putUint64 b4 _ M.prev $$ [$Hb $Hbc] as %b5 ⟨Hb, Hbc⟩
  wp_apply wp_putUint64 b5 _ M.prevTerm $$ [$Hb $Hbc] as %b6 ⟨Hb, Hbc⟩
  ihave #HentsO' := HentsO
  iunfold entsRO at HentsO'
  iunfold entsPts at HentsO'
  icases HentsO' with ⟨%ls, #Hls, #Hbig⟩
  ihave %Hbl := entsBig_length $$ Hbig
  ihave %Hlen := ownSlice_len $$ Hls
  wp_apply wp_putUint64 b6 _ es.len $$ [$Hb $Hbc] as %b7 ⟨Hb, Hbc⟩
  generalize HB0 : ([] ++ u64Le M.hs.Term' ++ u64Le M.hs.Vote' ++ u64Le M.hs.Commit' ++
    encSnap M.snap ++ u64Le M.prev ++ u64Le M.prevTerm ++ u64Le es.len) = B0
  -- the entries, in order
  ihave IH : iprop(∃ (j : w64) (bv : GoSlice) (x : Loc),
      "i" ∷ i_ptr ↦ j ∗ "buf" ∷ buf_ptr ↦ bv ∗
      "Hb" ∷ bv ↦* (B0 ++ encEntries (M.ents.take (sint.nat j))) ∗
      "Hbc" ∷ ownSliceCap w8 bv (DFrac.own 1) ∗ "e" ∷ e_ptr ↦ x ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z es.len⌝)
    $$ [i buf Hb Hbc e]
  · iexists W64 0, b7, _
    iframe
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, encEntries, List.append_nil]
    iframe
    ipureintro; exact ⟨by decide, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hjl : sint.nat j < M.ents.length := by rw [← Hbl, Hlen.1]; word
    obtain ⟨x0, Hx0⟩ : ∃ x0, M.ents[sint.nat j]? = some x0 := ⟨_, List.getElem?_eq_getElem Hjl⟩
    icases entsBig_lookup ls M.ents (sint.nat j) x0 Hx0 $$ Hbig with ⟨%l, %Hl, #Hel⟩
    try wp_auto
    rw [ite_eq_left (by omega)]
    wp_apply wp_load_slice_index es (sint.Z j) ls DFrac.discard l Hj.1 $$ [$Hls] as -
    · ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact Hl
    try wp_auto
    wp_apply wp_putEntry bv _ l DFrac.discard x0 $$ [$Hb $Hbc $Hel] as %b1 ⟨Hb, Hbc, -⟩
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, b1, l
    have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have Htk : M.ents.take (sint.nat j + 1) = M.ents.take (sint.nat j) ++ [x0] := by
      rw [List.take_add_one, Hx0]; rfl
    rw [Hj1, Htk, encEntries_snoc]
    simp only [List.append_assoc]
    iframe
    ipureintro; constructor <;> word
  · have Hjk : sint.nat j = M.ents.length := by rw [← Hbl, Hlen.1]; word
    rw [Hjk, List.take_length] at *
    try wp_auto
    iapply HΦ
    iframe
    isplitl [Hb]
    · have Hxl : es.len = W64 M.ents.length := by rw [← Hbl, Hlen.1]; have := Hlen.2; word
      rw [← HB0, Hxl]
      simp only [encStor, List.nil_append, List.append_assoc]
      iexact Hb
    iunfold ownImage
    iexists hsp, sp, es
    iframe # ∗
    ipureintro; exact Hwf

end proof

end kvdurable
end EtcdGrove
end Perennial
