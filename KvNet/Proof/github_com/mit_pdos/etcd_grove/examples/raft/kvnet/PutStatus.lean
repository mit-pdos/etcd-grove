/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/PutStatus.lean`. Lean-first (no Rocq
counterpart): the index, the configuration (`putConfState`), the store's copy (`putMap`), four
counters from a slice literal and the stats' array, each appended with `putUint64`; the loops keep the
buffer (its bytes and capacity).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.PutStatus
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putUint64
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putConfState
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putMap

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem PutStatus.wp_proof
    (wp_putUint64 : putUint64.spec (GF := GF) (hG := hG))
    (wp_putConfState : putConfState.spec (GF := GF) (hG := hG))
    (wp_putMap : putMap.spec (GF := GF) (hG := hG)) :
    PutStatus.spec (GF := GF) (hG := hG) := by
  intro s M dq c HSt
  wp_start as ⟨HM, #Hcs⟩
  ihave Hb0 : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hc0 : ownSliceCap w8 slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  try wp_auto
  wp_apply wp_putUint64 slice.nil [] s.Index' $$ [$Hpkg $Hb0 $Hc0] as %b1 ⟨Hb1, Hc1⟩
  try wp_auto
  wp_apply wp_putConfState b1 _ s.Conf' DFrac.discard c $$ [$Hpkg $Hb1 $Hc1 $Hcs] as %b2 ⟨Hb2, Hc2, -⟩
  try wp_auto
  wp_apply wp_putMap b2 _ s.Contents' M dq $$ [$Hpkg $Hb2 $Hc2 $HM] as %b3 ⟨HM, Hc3, %kvs, Hb3, -⟩
  try wp_auto
  -- the four counters, from a slice literal
  wp_apply wp_slice_literal (V := w64) [s.Lead', s.Term', s.Role', s.Commit']
  isplitr
  · ipureintro; rfl
  iintro %ls ⟨Hls, -⟩
  rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.uint64 #s.Lead'),
    KeyedElement none (ElementExpression go.uint64 #s.Term'),
    KeyedElement none (ElementExpression go.uint64 #s.Role'),
    KeyedElement none (ElementExpression go.uint64 #s.Commit')] = 4 from rfl]
  imod ownSlice_persist (slice.mk ls (W64 4) (W64 4)) _ _ $$ Hls with #Hls
  ihave %Hlsl := ownSlice_len $$ Hls
  try wp_auto
  ihave IH : iprop(∃ (k : w64) (bv : GoSlice) (B : List w8) (x0 : w64),
      "i" ∷ i_ptr ↦ k ∗ "buf" ∷ buf_ptr ↦ bv ∗ "Hb" ∷ bv ↦* B ∗
      "Hc" ∷ ownSliceCap w8 bv (DFrac.own 1) ∗ "x" ∷ x_ptr ↦ x0 ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 4⌝) $$ [i buf Hb3 Hc3 x]
  · iexists W64 0, b3, _, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · obtain ⟨v, Hv⟩ : ∃ v, [s.Lead', s.Term', s.Role', s.Commit'][sint.nat k]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by simp only [List.length_cons, List.length_nil]; word)⟩
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z (slice.mk ls (W64 4) (W64 4)).len := ⟨Hk.1, by word⟩
    (try wp_auto)
    try rw [ite_eq_left Hbnd]
    icases ownSlice_elem_acc (sint.Z k) v (slice.mk ls (W64 4) (W64 4)) DFrac.discard _ Hk.1 Hv $$ Hls
      with ⟨#Hle, -⟩
    (try wp_auto)
    wp_apply wp_putUint64 bv B v $$ [$Hpkg $Hb $Hc] as %b' ⟨Hb', Hc'⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists k + W64 1, b', _, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  (try wp_auto)
  -- the counters' count, then the stats' array
  wp_apply wp_putUint64 bv B (W64 numStats) $$ [$Hpkg $Hb $Hc] as %b4 ⟨Hb4, Hc4⟩
  try wp_auto
  ihave IH2 : iprop(∃ (k : w64) (bv : GoSlice) (B : List w8) (x0 : w64),
      "i" ∷ i_ptr ↦ k ∗ "buf" ∷ buf_ptr ↦ bv ∗ "Hb" ∷ bv ↦* B ∗
      "Hc" ∷ ownSliceCap w8 bv (DFrac.own 1) ∗ "x" ∷ x_ptr ↦ x0 ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ numStats⌝) $$ [i buf Hb4 Hc4 x]
  · iexists W64 0, b4, _, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH2
  wp_if_destruct
  · have Hlt : sint.nat k < s.Stats'.arr.length := by
      have h2 : sint.Z k < numStats := by word
      rw [HSt]; exact (Int.toNat_lt_toNat (by decide)).2 h2
    obtain ⟨v, Hv⟩ : ∃ v, s.Stats'.arr[sint.nat k]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [if_pos Hk.1, Hv]
    (try wp_auto)
    wp_apply wp_putUint64 bv B v $$ [$Hpkg $Hb $Hc] as %b' ⟨Hb', Hc'⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists k + W64 1, b', _, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  (try wp_auto)
  iapply HΦ
  iexists _
  iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
