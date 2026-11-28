/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/followerReplication__notifyAll.lean (241f27e).
-/
/-
The proof of `followerReplication__notifyAll` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__notifyAll
public import Dsverify.Spec.github_com.hashicorp.raft.verifyFuture__vote
public import Dsverify.Proof.github_com.hashicorp.raft.ReplNotify

@[expose] public section

set_option linter.unusedVariables false

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

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot proto

theorem github_com.hashicorp.raft.followerReplication.notifyAll.wp_proof
    (wp_vote : github_com.hashicorp.raft.verifyFuture.vote.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.followerReplication.notifyAll.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j s b => by
  wp_start as ⟨#Hr, #Hs, %Hb⟩
  subst Hb
  ihave ⟨%vch, #Hvch, #Hnl⟩ := replShared_notify r γ rc i T j s $$ Hs
  ihave ⟨-, -, #Hvj, -⟩ := replShared_core r γ i T j s $$ Hs
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hnl] as ⟨Hlocked, Hinv⟩
  iunfold notifyInv at Hinv
  icases Hinv with ⟨%m, %M, Hn, Hm, HM⟩
  wp_auto
  wp_apply (wp_map_make1 (K := Loc) (V := Unit) (go.GoType.PointerType verifyFuture.ty)
    (go.GoType.StructType [])) as %m2 Hm2
  wp_apply sync.Mutex.wp_Unlock $$ [$Hnl $Hlocked Hn Hm2]
  · inext
    unfold notifyInv
    iexists m2, ∅
    iframe
    iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2
    iempintro
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range_gen (K := Loc) (V := Unit) (fun keys (idx : Nat) mm => iprop(⌜mm = M⌝ ∗
      ∃ x : Loc, v_ptr ↦ x ∗ leader_ptr ↦ false ∗
      [∗list] k ∈ keys.drop idx, notifyEntry γ rc i T vch j k))) $$ Hm
  iintro %keys %hkeys
  obtain ⟨hkm, hksz, hknd⟩ := hkeys
  isplitl [v leader HM]
  · isplitr; · ipureintro; rfl
    iexists _
    iframe
    simp only [List.drop_zero]
    iapply bigSepM_keys_loc _ keys M hknd hkm $$ HM
  isplitl []
  · imodintro
    iintro %idx %key %u %mm ⟨%hk1, %hk2⟩ ⟨%hm, %x, v, leader, Hl⟩ Hm
    subst mm
    have hjl : idx < keys.length := (List.getElem?_eq_some_iff.mp hk1).1
    rw [List.drop_eq_getElem_cons hjl, (List.getElem?_eq_some_iff.mp hk1).2]
    ihave ⟨Hk, Hl⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    iunfold notifyEntry at Hk
    icases Hk with ⟨%sv, %L, #Hsv, #Hreg, -, -⟩
    wp_auto
    wp_apply (wp_vote r γ rc i T sv L vch j key false)
    · iframe #
      ileft; ipureintro; rfl
    unfold forMapPostcondition
    iright; ileft
    isplitr; · ipureintro; rfl
    iexists M
    iframe Hm
    isplitr; · ipureintro; rfl
    iexists key
    iframe
  isplitl []
  · imodintro
    iintro %idx %key %mm ⟨%hk1, %hk2⟩ ⟨%hm, -⟩
    subst mm
    exact absurd ((hkm key).mp (List.mem_of_getElem? hk1)) (by rw [hk2]; simp)
  iintro %mm ⟨%hm, -⟩ Hm
  subst mm
  wp_auto
  iapply HΦ; itrivial

end proof

end Perennial
