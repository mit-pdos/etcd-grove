/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/entryOf.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.entryOf
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootData

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]


variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem entryOf.wp_proof
    (wp_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_bootData : bootData.spec (GF := GF) (hG := hG)) :
    entryOf.spec (GF := GF) (hG := hG) := by
  intro p dq e nn hty
  wp_start as Hp
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  by_cases hb : e.Index' = W64 1 ∧ e.Data' = AntSim.bootData
  · wp_apply wp_GetIndex.1 p dq e $$ [$Hpb $Hp] as Hp
    try wp_auto
    rw [decide_eq_true hb.1]
    try wp_auto
    wp_apply wp_GetData.1 p dq e $$ [$Hpb $Hp] as %ds0 ⟨#Hd0, Hp⟩
    try wp_auto
    wp_apply wp_bytes_to_string ds0 e.Data' DFrac.discard $$ [$Hd0] as -
    wp_apply wp_bootData $$ [$Hpkg] as %bs Hbs
    wp_apply wp_bytes_to_string bs AntSim.bootData (DFrac.own 1) $$ [$Hbs] as -
    try wp_auto
    rw [decide_eq_true hb.2]
    try wp_auto
    wp_apply wp_GetTerm.1 p dq e $$ [$Hpb $Hp] as Hp
    try wp_auto
    iapply HΦ
    iframe Hp
    ihave #Hnil := ownSlice_nil (V := GoString) (GF := GF) DFrac.discard
    unfold entOfE
    rw [if_pos hb]
    iunfold AntCheck.entryRO
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iunfold AntCheck.valueRO
    iunfold AntCheck.strsRO
    iframe Hnil
    ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  have hnb := hb
  wp_join at next with [Hp e]
  · wp_apply wp_GetIndex.1 p dq e $$ [$Hpb $Hp] as Hp
    try wp_auto
    wp_if_destruct
    · wp_apply wp_GetData.1 p dq e $$ [$Hpb $Hp] as %ds0 ⟨#Hd0, Hp⟩
      try wp_auto
      wp_apply wp_bytes_to_string ds0 e.Data' DFrac.discard $$ [$Hd0] as -
      wp_apply wp_bootData $$ [$Hpkg] as %bs Hbs
      wp_apply wp_bytes_to_string bs AntSim.bootData (DFrac.own 1) $$ [$Hbs] as -
      try wp_auto
      rw [decide_eq_false (fun h => hb ⟨Hif, h⟩)]
      try wp_auto
      wp_join_done
    · try wp_auto
      wp_join_done
  wp_apply wp_GetType.1 p dq e $$ [$Hpb $Hp] as Hp
  try wp_auto
  rw [hty]
  try wp_auto
  wp_apply wp_GetData.1 p dq e $$ [$Hpb $Hp] as %ds ⟨#Hd, Hp⟩
  ihave %Hdl := ownSlice_len $$ Hd
  try wp_auto
  ihave #Hnil := ownSlice_nil (V := GoString) (GF := GF) DFrac.discard
  wp_if_destruct
  · have hd : e.Data' = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hdl.1, Hif]; rfl
    wp_apply wp_GetTerm.1 p dq e $$ [$Hpb $Hp] as Hp
    try wp_auto
    iapply HΦ
    iframe Hp
    unfold entOfE
    rw [if_neg hnb, if_pos hd]
    iunfold AntCheck.entryRO
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iunfold AntCheck.valueRO
    iunfold AntCheck.strsRO
    iframe Hnil
    ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  · have hd : e.Data' ≠ [] := by
      intro h
      apply Hif
      have h0 : sint.nat ds.len = 0 := by rw [← Hdl.1, h]; rfl
      have h1 : sint.Z ds.len = 0 := by
        have := Hdl.2
        have h2 : sint.nat ds.len = (sint.Z ds.len).toNat := rfl
        omega
      word
    wp_apply wp_GetTerm.1 p dq e $$ [$Hpb $Hp] as Hp
    try wp_auto
    wp_apply wp_GetData.1 p dq e $$ [$Hpb $Hp] as %ds' ⟨#Hd', Hp⟩
    try wp_auto
    wp_apply wp_bytes_to_string ds' e.Data' DFrac.discard $$ [$Hd'] as -
    try wp_auto
    iapply HΦ
    iframe Hp
    unfold entOfE
    rw [if_neg hnb, if_neg hd]
    iunfold AntCheck.entryRO
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iunfold AntCheck.valueRO
    iunfold AntCheck.strsRO
    iframe Hnil
    ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩

end proof

end AntHarness
end EtcdGrove
end Perennial
