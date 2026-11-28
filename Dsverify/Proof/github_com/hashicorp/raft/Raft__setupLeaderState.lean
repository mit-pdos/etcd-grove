/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__setupLeaderState.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).setupLeaderState`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setupLeaderState
public import Dsverify.Proof.github_com.hashicorp.raft.leader.MainCfg
public import Dsverify.Spec.github_com.hashicorp.raft.newCommitment
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastIndex

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.setupLeaderState.wp_proof
    (wp_newCommitment : github_com.hashicorp.raft.newCommitment.spec (GF := GF) (hG := hG))
    (wp_getLastIndex : github_com.hashicorp.raft.raftState.getLastIndex.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.setupLeaderState.spec (GF := GF) (hG := hG) :=
  fun r γ rc i s => by
  wp_start as ⟨#Hr, Hm, #Hlen0, Hcc2, Hany⟩
  ihave ⟨#HInv, #Hvoter⟩ := isRaft_proto r γ rc i $$ Hr
  ihave %Hcv := isRaft_cv r γ rc i $$ Hr
  ihave #Hdur := isRaft_durInv r γ rc i $$ Hr
  ihave ⟨%a, Hsrv, Hpw, HlastLog, Happ, %Ha, #Hldr, Hrest, Hconf⟩ := mainOwnAt_lopen r γ rc i s $$ Hm
  iunfold confOwn at Hconf
  icases Hconf with ⟨%cfg, %ccfg, %cidx, %li, Hconfs, #Hcfg, #Hccfg, %Hli, #Hcmt, Hccm, %n0, #Hn0, Hcix, #Hcl⟩
  imod ccfgOwn_entry γ ⊤ (by solve_ndisj) i s.term (lastCfgIdx s.log) $$ [Hcc2] with ⟨Hcc2, %e0, #He0, %He0k⟩
  · iframe; iframe #
  iapply wp_ncmod _ _ rfl (srvV_llogIdx_leader γ rc i s (lastCfgIdx s.log) e0)
  isplitl [Hsrv]
  · iframe; iframe #
  iintro ⟨Hsrv, %Hent0⟩
  have hli1 : 1 ≤ uint.nat li := by rw [Hli.1]; exact (proto.ent_le_length Hent0).1
  ihave Hcfg' := Hcfg
  iunfold cfgAtIs at Hcfg'
  icases Hcfg' with (⟨%h0, -⟩ | ⟨%ss, %ec, #Hcv0, %Hec⟩)
  · exfalso; omega
  have hec : ec = e0 := by
    have := Hec.2.1; rw [Hli.1, Hent0] at this; exact (Option.some.inj this).symm
  subst hec
  ihave #Hchans := isRaft_chans r γ rc i $$ Hr
  unfold raftChans
  icases Hchans with ⟨-, ⟨%vch, #Hvch, -⟩, -⟩
  iapply wp_ncmod _ _ rfl (srvV_facts γ rc i s)
  isplitl [Hsrv]
  · iframe; iframe #
  iintro ⟨Hsrv, -, %Hfacts⟩
  obtain ⟨-, -, -, -, -, -, Hloglt, -, -⟩ := Hfacts
  unfold leaderStateAny
  icases Hany with ⟨%cc0, %cm0, %infl0, %rs0, %nt0, %sd0, HNMa, Hcc, Hcm, Hinfl, Hrs, Hnt, Hsd⟩
  wp_auto
  wp_apply (chan.wp_make2 (V := Unit) (W64 1)) as %cc %γcc ⟨#Hccch, %Hγcc, Hccown⟩
  · ipureintro; word
  imod (start_bag (fun _ => iprop(True)) _ cc γcc trivial) $$ Hccch Hccown with #Hccb
  wp_apply (wp_getLastIndex.1 r γ rc i s a) $$ [$Hr $HlastLog $Hsrv $Happ]
    as %li' ⟨%Hli', HlastLog, Hsrv, Happ⟩
  · ipureintro; exact Ha.1
  wp_apply (wp_newCommitment γ i s.term s.log.length (lastCfgIdx s.log) cc cfg ss ec (li' + W64 1))
    $$ [$HInv $Hcv0 $He0 $Hcc2 $Hldr $Hlen0] as %cm #Hcmi
  · isplitr; · unfold notifyChan; iexists γcc; iexact Hccb
    ipureintro; exact ⟨⟨He0k, Hec.2.2.2, Hcv⟩, by word⟩
  wp_apply (wp_slice_make2 (V := Loc) (W64 0)) as %infl ⟨Hinfls, Hinflc⟩
  · ipureintro; word
  wp_apply (wp_map_make1 (K := SID) (V := Loc) ServerID.ty (go.GoType.PointerType followerReplication.ty))
    as %rs Hrsm
  wp_apply (wp_map_make1 (K := Loc) (V := Unit) (go.GoType.PointerType verifyFuture.ty)
    (go.GoType.StructType [])) as %nt Hntm
  wp_apply +noauto (chan.wp_make2 (V := Unit) (W64 1)) as %sd %γsd ⟨#Hsdch, %Hγsd, Hsdown⟩
  · ipureintro; word
  imod (start_bag (fun _ => iprop(True)) _ sd γsd trivial) $$ Hsdch Hsdown with #Hsdb
  wp_auto
  iapply HΦ
  isplitl [Hsrv Hpw HlastLog Happ Hrest Hconfs Hccm Hcix]
  · iapply mainOwnAt_lclose r γ rc i s a
    iframe Hsrv Hpw HlastLog Happ Hrest
    iframe #
    isplitr; · ipureintro; exact Ha
    iapply confOwn_intro r γ i s a cfg ccfg cidx li n0 Hli
    iframe; iframe #
  ihave HNMp : (∃ (NM' : GMap Loc Unit) (vch' : Loc), nt ↦$ NM' ∗
      ghostMapAuth rc.names.vnm (1 : Qp).half NM' ∗ r.[Raft, go!"verifyCh"] ↦□ vch' ∗
      [∗map] w ↦ _u ∈ NM', leaderNotifyEntry γ rc i s.term vch' w : IProp GF) $$ [Hntm HNMa]
  · iexists ∅, vch; iframe; iframe #
    iapply BigSepM.bigSepM_empty.2; iempintro
  unfold leaderOwnM
  iexists cc, cm, infl, [], rs, ∅, nt, sd, s.log.length
  iframe; iframe #
  unfold notifyChan
  isplitr; · iexists γcc; iexact Hccb
  isplitr; · ipureintro; simp
  isplitr; · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitr; · iapply BigSepM.bigSepM_empty.2; iempintro
  isplitr; · iexists γsd; iexact Hsdb
  isplitr; · ipureintro; rfl
  iexists 0
  isplitr; · ileft; ipureintro; rfl
  ipureintro; refine ⟨Nat.le_refl _, fun k hk1 hk2 => ?_⟩; exfalso; simp at hk1; omega

end proof

end Perennial
