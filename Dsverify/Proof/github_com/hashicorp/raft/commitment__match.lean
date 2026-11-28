/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/commitment__match.lean (241f27e).
-/
/-
The proof of `commitment__match` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.commitment__match
public import Dsverify.Spec.github_com.hashicorp.raft.commitment__recalculate

@[expose] public section

set_option linter.unusedVariables false
set_option linter.deprecated false

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

theorem github_com.hashicorp.raft.commitment.match.wp_proof
    (wp_recalculate : github_com.hashicorp.raft.commitment.recalculate.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.commitment.match.spec (GF := GF) (hG := hG) :=
  fun γ i T cm j k => by
  wp_start as ⟨#Hcm, #Hk⟩
  wp_apply wp_with_defer as %defer Hdefer
  unfold isCommitment
  icases Hcm with ⟨-, #Hcm⟩
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hcm] as ⟨Hlocked, Hinv⟩
  unfold commitInv
  icases Hinv with ⟨%ch, %mi, %mm, %ci, %si, %n0, %p, %e, Hch, #Hchn, Hmi, Hmm, Hcc, #He, %Hdom, Hacks, Hci, #Hcio, #Hsip, #Hn0, %Hsi, #Hl, #HInv⟩
  wp_auto
  wp_apply (wp_map_lookup2 (K := SID) (V := w64) ServerID.ty go.uint64 mi mm j (DFrac.own 1)) $$ [$Hmm] as Hmm
  cases hj : mm !! j with
  | none =>
    wp_auto
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hcm $Hlocked Hch Hmi Hmm Hacks Hci Hcc]
    · inext
      iexists ch, mi, mm, ci, si, n0, p, e
      iframe; iframe #
      ipureintro; exact ⟨Hdom, Hsi⟩
    iapply HΦ; itrivial
  | some prev =>
    wp_if_destruct
    rotate_left
    · exfalso; simp at Hif
    wp_if_destruct
    · -- `j` has a vote and `k` is past its match index: record it and recalculate
      have hk0 : uint.nat k ≠ 0 := by word
      icases Hk with (%h0 | #Hack)
      · exfalso; exact hk0 h0
      wp_apply (wp_mapInsert (K := SID) (V := w64) ServerID.ty mi mm j k) $$ [$Hmm] as Hmm
      ihave ⟨-, Hacks⟩ := BigSepM.bigSepM_insert_acc (Φ := fun j m => iprop(⌜m = W64 0⌝ ∨ ackIs (GF := GF) γ j T (uint.nat m) ∨ lciOk γ T (uint.nat m))) (m := mm) hj $$ Hacks
      ihave Hacks := Hacks $$ %k []
      · iright; iexact Hack
      wp_apply (wp_recalculate γ i T cm) $$ [Hch Hmi Hmm Hacks Hci Hcc] as Hinv
      · unfold commitInv
        iexists ch, mi, (<[j := k]> mm), ci, si, n0, p, e
        iframe; iframe #
        ipureintro
        refine ⟨⟨Hdom.1, ?_, Hdom.2.2⟩, Hsi⟩
        intro j'
        rw [← Hdom.2.1 j']
        by_cases hjj : j = j'
        · subst hjj; simp [hj]
        · rw [GMap.lookup_insert_ne _ _ hjj]
      wp_method_call
      wp_call
      wp_apply sync.Mutex.wp_Unlock $$ [$Hcm $Hlocked Hinv]
      · inext; unfold commitInv; iexact Hinv
      iapply HΦ; itrivial
    · wp_method_call
      wp_call
      wp_apply sync.Mutex.wp_Unlock $$ [$Hcm $Hlocked Hch Hmi Hmm Hacks Hci Hcc]
      · inext
        iexists ch, mi, mm, ci, si, n0, p, e
        iframe; iframe #
        ipureintro; exact ⟨Hdom, Hsi⟩
      iapply HΦ; itrivial
