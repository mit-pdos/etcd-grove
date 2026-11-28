/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__restoreSnapshot.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).restoreSnapshot`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__restoreSnapshot

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

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.Raft.restoreSnapshot.wp_proof :
    github_com.hashicorp.raft.Raft.restoreSnapshot.spec (GF := GF) (hG := hG) := by
  intro r x ownSS eof tid
  wp_start as ⟨#Hsn, #Hss, Hown, Htok⟩
  wp_auto
  unfold isSnapStore
  icases Hss with ⟨-, #HList, -⟩
  wp_bind
  iapply HList $$ Htok
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists none
  iframe Hown
  iintro Hown
  imod Hmask with -
  imodintro
  iintro %sl %ps Hs %Hps Htok
  subst Hps
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_for
  wp_if_destruct
  · simp at Hlen; word
  · wp_if_destruct
    · simp at Hlen; word
    · wp_end

end proof

end Perennial
