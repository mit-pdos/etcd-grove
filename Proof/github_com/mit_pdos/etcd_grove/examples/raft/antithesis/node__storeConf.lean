/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__storeConf.lean`: the detached
storage's snapshot (`MemoryStorage.Snapshot`) is at index `0`, so the configuration is the run's
initial voters (a fresh `ConfState`, frozen).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__storeBase
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__storeConf
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

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

theorem node.storeConf.wp_proof (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_MdGetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    node.storeConf.spec (GF := GF) (hG := hG) := by
  intro c γ n j ms γs h sv hsv
  wp_start as ⟨#Hc, #Hn, Hst, #Hlock, Hmeta, Hfresh⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  iunfold clusterRO at Hro
  icases Hro with ⟨%nsl, %ivl, #Hns, #Hnsl, %HN, #Hmd, #Hiv, #Hivs⟩
  iunfold nodeRO at Hn
  icases Hn with ⟨%ch, %d, #Hnc, #Hid, #Hname, #Hin, #Hbag, #Hd, #Hlog⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave Hinit := isInitialized_access $$ Hraft
  unfold isInitialized
  iNamed Hinit
  try wp_auto
  ihave Hat : memStorAt ms γs storeJ (some (0, sv)) emp $$ [Hfresh]
  · simp only [memStorAt]; iframe Hlock Hfresh
  ihave #Hc0 := memCompacted_zero γs
  wp_apply wp_Snapshot ms γs storeJ (some (0, sv)) 0 none _ $$ [$Hraft $Hat $Hc0 $ErrSnapUnavail]
    as %snap %err ⟨-, %Herr, %sv', Hs, %Hsv, Ho⟩
  subst Herr
  icases Ho with ⟨%Heq, Hfresh⟩
  subst Heq
  ihave Hs := ownSnapW_E $$ Hs
  ihave Hs := ownSnapE_weaken $$ Hs
  try wp_auto
  wp_apply wp_GetMetadata.1 snap _ sv' $$ [$Hpb $Hs] as %pm ⟨Hpm, -⟩
  wp_apply wp_MdGetIndex pm _ _ $$ [$Hpb $Hpm] as -
  rw [hsv]
  iapply wp_fupd
  try wp_auto
  have hK : γ.R.K = uint.nat γ.mode.Voters' := Hmode.2.2.1
  imod csPts_of_struct_ro «$r0_ptr»
      (⟨zeroValDef, ivl, slice.nil, slice.nil, slice.nil, null, slice.nil, 0⟩ : raftpb.ConfState)
      (ConfStateM.mk ((List.range γ.R.K).map fun (i : Nat) => W64 ((i : Int) + 1)) [] [] [] false) ⊤ rfl
      $$ [«$r0»] with #Hcs
  · iframe «$r0»
    rw [hK]
    iframe Hivs
    repeat (isplitr; · iapply ownSlice_nil)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  imodintro
  iapply HΦ
  iframe Hst Hmeta Hfresh
  have hdec : decide ((null : Loc) ≠ null) = false := decide_eq_false (fun h => h rfl)
  rw [← hdec]
  iexact Hcs

end proof

end AntHarness
end EtcdGrove
end Perennial
