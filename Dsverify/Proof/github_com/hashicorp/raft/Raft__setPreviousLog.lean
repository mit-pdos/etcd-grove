/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__setPreviousLog.lean (241f27e).
-/
/-
The proof of `Raft__setPreviousLog` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setPreviousLog
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastSnapshot
public import Dsverify.Proof.github_com.hashicorp.raft.ReplSnap

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

theorem github_com.hashicorp.raft.Raft.setPreviousLog.wp_proof
    (wp_getLastSnapshot : github_com.hashicorp.raft.raftState.getLastSnapshot.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.setPreviousLog.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T req rq nextIndex tid => by
  wp_start as ⟨#Hr, #Hl, #Hlb, Hreq, Htok⟩
  iapply wp_fupd
  wp_auto
  wp_apply wp_getLastSnapshot $$ [$Hr] as %si %st #Hsn
  wp_if_destruct
  · -- nextIndex = 1: no previous entry
    imodintro
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; exact ⟨rfl, by word⟩
    ileft; unfold prevOk; ileft; ipureintro; exact ⟨by word, by word⟩
  wp_if_destruct
  · -- the previous entry is the last snapshot (`si = nextIndex - 1`)
    icases Hsn with (%Hsi | ⟨%e, #Hc, %He, -, #Hdf⟩)
    · exfalso; apply Hif; word
    have hsi : 1 ≤ uint.nat (nextIndex - W64 1) := by
      have : nextIndex - W64 1 ≠ W64 0 := by intro h; apply Hif; word
      word
    ihave ⟨#Hinv, #Hv⟩ := isRaft_proto r γ rc i $$ Hr
    imod CIdx_lt γ ⊤ (by solve_ndisj) (uint.nat (nextIndex - W64 1)) e $$ [] with %hlt
    · iframe #
    have hpn : uint.nat (nextIndex - W64 1) + 1 = uint.nat nextIndex := by word
    imod snap_valid γ i T (uint.nat (nextIndex - W64 1)) (uint.nat st) e hsi $$ [] with (#Hae | #Hst)
    · iframe #; ipureintro; exact He
    · iapply HΦ
      iframe Htok
      iexists (nextIndex - W64 1), st
      iframe Hreq
      iright
      isplitr
      · ipureintro; exact ⟨rfl, hpn⟩
      ileft; iapply aeValid_prevOk γ T _ _ [] _ $$ Hae
    · iapply HΦ
      iframe Htok
      iexists (nextIndex - W64 1), st
      iframe Hreq
      iright
      isplitr
      · ipureintro; exact ⟨rfl, hpn⟩
      iright; iexact Hst
  ihave ⟨%x, #Hlogs, #Hls, -⟩ := isRaft_logStore r γ rc i $$ Hr
  ihave ⟨#Hinv, -⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Hcell := isRaft_logCell r γ rc i $$ Hr
  wp_load
  wp_pures
  wp_apply (wp_getLog_repl γ rc i T x (nextIndex - W64 1) l_ptr _) $$ [$l $Htok] as %err ⟨Htok, Hres⟩
  · iframe #
  unfold getLogRepl
  icases Hres with (⟨%Herr, #Hce, %lv, Hlv⟩ | ⟨%Herr, %lv, %e, Hlv, #His, %Hk, #Hrd⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok erri =>
    wp_auto
    imodintro
    iapply HΦ
    iframe
    ileft; iframe #; ipureintro; exact Herr
  · subst Herr
    wp_auto
    ihave #His2 := His
    unfold logIs
    icases His2 with ⟨%Hlv, -⟩
    obtain ⟨Hidx, Hterm, -⟩ := Hlv
    imodintro
    iapply HΦ
    iframe Htok
    iexists lv.Index', lv.Term'
    iframe Hreq
    iright
    isplitr
    · ipureintro; refine ⟨rfl, ?_⟩; rw [Hidx]; word
    rw [Hidx]
    icases Hrd with (#Hrd | #Hrd)
    · ileft; unfold prevOk; iright; iexists e
      isplitr
      · ipureintro; exact ⟨Hk.1, Hterm.symm⟩
      iexact Hrd
    · iright; iexact Hrd

end proof

end Perennial
