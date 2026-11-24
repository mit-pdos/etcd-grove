/-
Proof of `checker.changeID`: the conf state's voters, outgoing voters and learners appended into a
fresh slice (`GetVoters`, ... on the read-only `cs`); with none, or one time in four, `randomID`;
else the element at `below(len)`, one of them.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__changeID
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__randomID
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.below
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.oneIn
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVoters
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetLearners

@[expose] public section

set_option linter.iris.style.nameCheck false

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]

theorem checker.changeID.wp_proof (wp_randomID : checker.randomID.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_GetVoters : raftpb.ConfState.GetVoters.spec (GF := GF) (hG := hG))
    (wp_GetVotersOutgoing : raftpb.ConfState.GetVotersOutgoing.spec (GF := GF) (hG := hG))
    (wp_GetLearners : raftpb.ConfState.GetLearners.spec (GF := GF) (hG := hG)) :
    checker.changeID.spec (GF := GF) (hG := hG) := by
  intro c γ ls csp cs Hne
  wp_start as ⟨#Hc, #Hcs⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_GetVoters csp DFrac.discard cs $$ [$Hpb $Hcs] as %sv ⟨#Hsv, -⟩
  ihave Hnil := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
  ihave Hncap := ownSliceCap_nil (V := w64) (GF := GF)
  wp_apply wp_slice_append slice.nil [] sv cs.Voters' DFrac.discard $$ [$Hnil $Hncap $Hsv]
    as %m1 ⟨Hm1, Hm1cap, -⟩
  wp_apply wp_GetVotersOutgoing csp DFrac.discard cs $$ [$Hpb $Hcs] as %so ⟨#Hso, -⟩
  wp_apply wp_slice_append m1 _ so cs.VotersOutgoing' DFrac.discard $$ [$Hm1 $Hm1cap $Hso]
    as %m2 ⟨Hm2, Hm2cap, -⟩
  wp_apply wp_GetLearners csp DFrac.discard cs $$ [$Hpb $Hcs] as %sl ⟨#Hsl, -⟩
  wp_apply wp_slice_append m2 _ sl cs.Learners' DFrac.discard $$ [$Hm2 $Hm2cap $Hsl]
    as %m3 ⟨Hm3, -, -⟩
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hm3
  wp_if_destruct
  · try wp_auto
    wp_apply wp_randomID c γ ls Hne $$ [$Hpkg $Hc] as %id %Hid
    try wp_auto
    iapply HΦ
    ipureintro; right; exact Hid
  · have Hlen0 := Hif
    wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b -
    wp_if_destruct
    · try wp_auto
      wp_apply wp_below as %k %Hk
      try wp_auto
      have Hk' := Hk.2 Hlen0
      have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z m3.len := by
        have := Hlen.2
        constructor <;> word
      rw [ite_eq_left Hb]
      have Hkn : sint.nat k < ([] ++ cs.Voters' ++ cs.VotersOutgoing' ++ cs.Learners').length := by
        rw [Hlen.1]; word
      obtain ⟨x, Hx⟩ : ∃ x, ([] ++ cs.Voters' ++ cs.VotersOutgoing' ++ cs.Learners')[sint.nat k]? = some x :=
        ⟨_, List.getElem?_eq_getElem Hkn⟩
      wp_apply wp_load_slice_index m3 (sint.Z k) _ _ x Hb.1 $$ [Hm3] as Hm3
      · iframe Hm3; ipureintro; exact Hx
      try wp_auto
      iapply HΦ
      ipureintro
      left
      have := List.mem_of_getElem? Hx
      simpa [List.append_assoc] using this
    · try wp_auto
      wp_apply wp_randomID c γ ls Hne $$ [$Hpkg $Hc] as %id %Hid
      try wp_auto
      iapply HΦ
      ipureintro; right; exact Hid

end proof

end raft_kvcheck
end EtcdGrove
end Perennial
