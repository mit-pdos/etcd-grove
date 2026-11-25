/-
The proof of `KvRaft/Spec/.../kvcheck/checker__randomMember.lean`: `lastConf` read under `mu` (its
conf state read-only, `checkerInv`), its voters and learners appended, and a member picked or a
random replica (`randomID`) when there is none, one time in four, or the member is out of range.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__randomMember
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__randomID
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.below
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.oneIn
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVoters
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetLearners
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]

theorem checker.randomMember.wp_proof (wp_randomID : checker.randomID.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_GetVoters : raftpb.ConfState.GetVoters.spec (GF := GF) (hG := hG))
    (wp_GetLearners : raftpb.ConfState.GetLearners.spec (GF := GF) (hG := hG)) :
    checker.randomMember.spec (GF := GF) (hG := hG) := by
  intro c γ ls Hne
  wp_start as #Hc
  ihave #Hc0 := Hc
  iunfold isChecker at Hc0
  icases Hc0 with ⟨%sl, #Ha, #Hsl, #Hmu⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold checkerInv at HL
  icases HL with ⟨%a, %b, %lc, %cs, Hop, Hrd, Hlc, #Hcs, HMa, HMb⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hop Hrd Hlc HMa HMb]
  · inext
    iunfold checkerInv
    iexists a, b, lc, cs
    iframe
    iframe Hcs
  try wp_auto
  wp_apply wp_GetVoters lc DFrac.discard cs $$ [$Hpb $Hcs] as %sv ⟨#Hsv, -⟩
  ihave Hnil := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
  ihave Hncap := ownSliceCap_nil (V := w64) (GF := GF)
  wp_apply wp_slice_append slice.nil [] sv cs.Voters' DFrac.discard $$ [$Hnil $Hncap $Hsv]
    as %m1 ⟨Hm1, Hm1cap, -⟩
  wp_apply wp_GetLearners lc DFrac.discard cs $$ [$Hpb $Hcs] as %sl2 ⟨#Hsl2, -⟩
  wp_apply wp_slice_append m1 _ sl2 cs.Learners' DFrac.discard $$ [$Hm1 $Hm1cap $Hsl2]
    as %m2 ⟨Hm2, -, -⟩
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hm2
  wp_if_destruct
  · try wp_auto
    wp_apply wp_randomID c γ ls Hne $$ [$Hpkg $Hc] as %id %Hid
    try wp_auto
    iapply HΦ
    ipureintro; exact Hid
  · have Hlen0 := Hif
    wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %bb -
    wp_if_destruct
    · try wp_auto
      wp_apply wp_below as %k %Hk
      try wp_auto
      have Hk' := Hk.2 Hlen0
      have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z m2.len := by
        have := Hlen.2
        constructor <;> word
      rw [ite_eq_left Hb]
      have Hkn : sint.nat k < ([] ++ cs.Voters' ++ cs.Learners').length := by
        rw [Hlen.1]; word
      obtain ⟨x, Hx⟩ : ∃ x, ([] ++ cs.Voters' ++ cs.Learners')[sint.nat k]? = some x :=
        ⟨_, List.getElem?_eq_getElem Hkn⟩
      wp_apply wp_load_slice_index m2 (sint.Z k) _ _ x Hb.1 $$ [Hm2] as Hm2
      · iframe Hm2; ipureintro; exact Hx
      try wp_auto
      ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
      wp_if_destruct
      · try wp_auto
        wp_apply wp_randomID c γ ls Hne $$ [$Hpkg $Hc] as %id %Hid
        try wp_auto
        iapply HΦ
        ipureintro; exact Hid
      · have Hx1 := Hif
        wp_if_destruct
        · try wp_auto
          wp_apply wp_randomID c γ ls Hne $$ [$Hpkg $Hc] as %id %Hid
          try wp_auto
          iapply HΦ
          ipureintro; exact Hid
        · try wp_auto
          iapply HΦ
          ipureintro
          have := Hsll.1; have := Hsll.2
          constructor <;> word
    · try wp_auto
      wp_apply wp_randomID c γ ls Hne $$ [$Hpkg $Hc] as %id %Hid
      try wp_auto
      iapply HΦ
      ipureintro; exact Hid

end proof

end raft_kvcheck
end EtcdGrove
end Perennial
