/-
The proof of `service.API.Read` (S6; the lab's hr3 `readAt`, 241f27e, restated for the kit's API).

Way 1: `Barrier` with the read's snapshot `sc`: `barrierOk` bounds every server's durable prefix at `sc`
below the barrier's index `b ≤ s`, and the FSM had processed `s` (`fsmAt`). Way 2: the term `t` read
first (a snapshot `s1 ⊒ sc` with `i`'s term `t`), a barrier of `t` (`barrierFact`, recorded in the API's
`barrierIn` or made now), `VerifyLeader` with `s1`: every server's prefix at `s1` is at most `len0 t`
(below the barrier's `s_b`) or at most `s_v` (`fsmAt s_v`); the two term reads pin the barrier's and the
verify's terms to `t`. Either way `sc.maxDur ≤ s` with `fsmAt s`; then `Store.read` gives the store's
prefix `es`, at least as long as what the FSM had applied at `s` (`k0`), and the read's claim
(`rdClaim`, with `noCmdBetween γ k0 (s + 1)` and `n0 ≤ sc.maxDur ≤ s`) gives `Ψ` of its register.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__Read
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.waitFuture
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.Store__read
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__Barrier
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__VerifyLeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__CurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__Error
public import Dsverify.Spec.github_com.hashicorp.raft.errorFuture__Error
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

set_option goose.wp.extras true

/-- A raft future is a non-nil interface value (`API.done`'s `futWait_ok`, restated here: a proof file
imports no proof). -/
private theorem futWait_ok_rd (fi : GoInterface) (Q : GoInterface → IProp GF) :
    futWait fi Q ⊢ futWait fi Q ∗ ⌜∃ x, fi = GoInterface.ok x⌝ := by
  iintro H
  ihave %h : ⌜∃ x, fi = GoInterface.ok x⌝ $$ [H]
  · unfold futWait
    icases H with (⟨%e, %hfi, -⟩ | ⟨%f, %hfi, -⟩ | ⟨%f, %hfi, -⟩ | ⟨%f, %hfi, -⟩ | ⟨%f, %hfi, -⟩ |
      ⟨%f, %hfi, -⟩) <;> ipureintro <;> exact ⟨_, hfi⟩
  iframe; ipureintro; exact h

theorem github_com.hashicorp.raft.examples.hraftnet.service.API.Read.wp_proof
    (wp_Barrier : github_com.hashicorp.raft.Raft.Barrier.spec (GF := GF) (hG := hG))
    (wp_VerifyLeader : github_com.hashicorp.raft.Raft.VerifyLeader.spec (GF := GF) (hG := hG))
    (wp_CurrentTerm : github_com.hashicorp.raft.Raft.CurrentTerm.spec (GF := GF) (hG := hG))
    (wp_waitFuture : github_com.hashicorp.raft.examples.hraftnet.service.waitFuture.spec (GF := GF) (hG := hG))
    (wp_dErr : github_com.hashicorp.raft.deferError.Error.spec (GF := GF) (hG := hG))
    (wp_eErr : github_com.hashicorp.raft.errorFuture.Error.spec (GF := GF) (hG := hG))
    (wp_read : github_com.hashicorp.raft.examples.hraftnet.service.Store.read.spec (GF := GF) (hG := hG))
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.service.API.Read.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)
