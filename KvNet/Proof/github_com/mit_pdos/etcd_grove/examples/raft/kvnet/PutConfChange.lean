/-
Proof of `KvNet/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/PutConfChange.lean`: the type
switch, then for a `ConfChange` its two getters, for a `ConfChangeV2` (`AsV2` is itself) its transition,
the changes' number and the loop over them (`ccsRO` of each).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.PutConfChange
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putUint64
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetType
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetNodeId
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__GetTransition
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__GetChanges
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeSingle__GetType
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeSingle__GetNodeId

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

theorem PutConfChange.wp_proof (wp_putUint64 : putUint64.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.ConfChange.GetType.spec (GF := GF) (hG := hG))
    (wp_GetNodeId : raftpb.ConfChange.GetNodeId.spec (GF := GF) (hG := hG))
    (wp_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (wp_GetTransition : raftpb.ConfChangeV2.GetTransition.spec (GF := GF) (hG := hG))
    (wp_GetChanges : raftpb.ConfChangeV2.GetChanges.spec (GF := GF) (hG := hG))
    (wp_sGetType : raftpb.ConfChangeSingle.GetType.spec (GF := GF) (hG := hG))
    (wp_sGetNodeId : raftpb.ConfChangeSingle.GetNodeId.spec (GF := GF) (hG := hG)) :
    PutConfChange.spec (GF := GF) (hG := hG) := by
  intro buf B cc dq o
  wp_start as ⟨Hbuf, Hcap, Hcc⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  cases o with
  | v1 m =>
    simp only [ownConfChangeI]
    icases Hcc with ⟨%p, %Hc, Hm⟩
    subst Hc
    wp_auto
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hbuf $Hcap $Hsl] as %b1 ⟨Hb, Hcap, -⟩
    try wp_auto
    wp_apply wp_GetType.1 p dq m $$ [$Hpb $Hm] as Hm
    try wp_auto
    wp_apply wp_putUint64 b1 _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
    try wp_auto
    wp_apply wp_GetNodeId.1 p dq m $$ [$Hpb $Hm] as Hm
    wp_apply wp_putUint64 b2 _ _ $$ [$Hb $Hcap] as %b3 ⟨Hb, Hcap⟩
    try wp_auto
    iapply HΦ
    simp only [encCC, List.append_assoc, List.singleton_append]
    iframe
    ipureintro; rfl
  | v2 m =>
    simp only [ownConfChangeI]
    icases Hcc with ⟨%p, %Hc, Hm⟩
    subst Hc
    try wp_auto
    wp_apply wp_AsV2 p $$ [$Hpb]
    try wp_auto
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hbuf $Hcap $Hsl] as %b1 ⟨Hb, Hcap, -⟩
    try wp_auto
    wp_apply wp_GetTransition.1 p dq m $$ [$Hpb $Hm] as Hm
    try wp_auto
    wp_apply wp_putUint64 b1 _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
    try wp_auto
    wp_apply wp_GetChanges.1 p dq m $$ [$Hpb $Hm] as %chs %ls ⟨Hch, #Hccs, Hback⟩
    ihave %Hll := BigSepL2.bigSepL2_length $$ Hccs
    ihave %Hlen := ownSlice_len $$ Hch
    ihave Hm := Hback $$ Hch
    try wp_auto
    wp_apply wp_putUint64 b2 _ _ $$ [$Hb $Hcap] as %b3 ⟨Hb, Hcap⟩
    have Hcl : chs.len = W64 m.changes.length := by rw [← Hll, Hlen.1]; have := Hlen.2; word
    rw [Hcl]
    generalize HB0 : B ++ [W8 2] ++ u64Le (W64 (sint.Z m.transition)) ++
      u64Le (W64 m.changes.length) = B0
    try wp_auto
    wp_apply wp_GetChanges.1 p dq m $$ [$Hpb $Hm] as %chs2 %ls2 ⟨Hch2, #Hccs2, Hback2⟩
    ihave %Hll2 := BigSepL2.bigSepL2_length $$ Hccs2
    ihave %Hlen2 := ownSlice_len $$ Hch2
    try wp_auto
    ihave IH : iprop(∃ (j : w64) (bv : GoSlice) (x : Loc),
        "i" ∷ i_ptr ↦ j ∗ "buf" ∷ buf_ptr ↦ bv ∗
        "Hb" ∷ bv ↦* (B0 ++ encCCSs (m.changes.take (sint.nat j))) ∗
        "Hcap" ∷ ownSliceCap w8 bv (DFrac.own 1) ∗ "c" ∷ c_ptr ↦ x ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z chs2.len⌝)
      $$ [i buf Hb Hcap c]
    · iexists W64 0, b3, _
      iframe
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, encCCSs, List.append_nil]
      iframe
      ipureintro; exact ⟨by decide, by word⟩
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.Z j < sint.Z chs2.len := by
        exact Hif
      have Hjl : sint.nat j < m.changes.length := by rw [← Hll2, Hlen2.1]; word
      have Hjl2 : sint.nat j < ls2.length := by rw [Hll2]; exact Hjl
      obtain ⟨x0, Hx0⟩ : ∃ x0, m.changes[sint.nat j]? = some x0 := ⟨_, List.getElem?_eq_getElem Hjl⟩
      obtain ⟨q, Hq⟩ : ∃ q, ls2[sint.nat j]? = some q := ⟨_, List.getElem?_eq_getElem Hjl2⟩
      ihave #Hq := BigSepL2.bigSepL2_lookup Hq Hx0 $$ Hccs2
      try wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z chs2.len from ⟨Hj.1, Hlt⟩)]
      wp_apply wp_load_slice_index chs2 (sint.Z j) ls2 dq q Hj.1 $$ [$Hch2] as Hch2
      · ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact Hq
      try wp_auto
      wp_apply wp_sGetType.1 q DFrac.discard x0 $$ [$Hpb $Hq] as -
      try wp_auto
      wp_apply wp_putUint64 bv _ _ $$ [$Hb $Hcap] as %b4 ⟨Hb, Hcap⟩
      try wp_auto
      wp_apply wp_sGetNodeId.1 q DFrac.discard x0 $$ [$Hpb $Hq] as -
      wp_apply wp_putUint64 b4 _ _ $$ [$Hb $Hcap] as %b5 ⟨Hb, Hcap⟩
      try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, b5, q
      have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have Htk : m.changes.take (sint.nat j + 1) = m.changes.take (sint.nat j) ++ [x0] := by
        rw [List.take_add_one, Hx0]; rfl
      rw [Hj1, Htk, encCCSs_snoc]
      simp only [encCCS, List.append_assoc]
      iframe
      ipureintro; constructor <;> word
    · have Hge : ¬ sint.Z j < sint.Z chs2.len := by
        exact Hif
      have Hjk : sint.nat j = m.changes.length := by rw [← Hll2, Hlen2.1]; word
      rw [Hjk, List.take_length]
      ihave Hm := Hback2 $$ Hch2
      try wp_auto
      iapply HΦ
      subst HB0
      simp only [encCC, List.append_assoc, List.singleton_append, List.cons_append]
      iframe
      ipureintro; rfl

end proof

end raft_kvnet
end EtcdGrove
end Perennial
