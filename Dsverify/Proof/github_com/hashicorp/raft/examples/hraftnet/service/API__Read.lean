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
  intro a args reply γ rc i fc alb way n0 sc Ψ
  wp_start as ⟨#Hapi, #Hargs, Hrep, #Hsc, %Hn0, Hcl⟩
  ihave #Hraft : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft) $$ []
  · iPkgInit
  ihave #Hapi' := Hapi
  iunfold isAPI at Hapi'
  icases Hapi' with ⟨%r, %fsm, %enq, %wt, #Hr, #Hfsm, #Henq, #Hwt, #Hisr, %Hresp, #Hst, #Hmu⟩
  have hfe := wp_futWait_Error wp_dErr.1 wp_dErr.2.1 wp_dErr.2.2.1 wp_dErr.2.2.2.1 wp_dErr.2.2.2.2.1 wp_eErr
  iStructNamed Hargs
  wp_auto
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗
      (∃ s, fsmAt γ (respP γ fc alb) i s ∗ ⌜sc.maxDur ≤ s⌝) ∗
      «$res0_ptr» ↦ GoInterface.nil ∗ a_ptr ↦ a ∗ r_ptr ↦ r) ∨
      (⌜v = returnVal #()⌝ ∗ «$res0_ptr» ↦ GoInterface.nil ∗ a_ptr ↦ a ∗ r_ptr ↦ r)))
    with [«$res0» a r]
  · -- way 1: a barrier after the read's snapshot
    wp_apply (wp_Barrier r γ rc i sc enq) $$ [$Hraft $Hisr $Hsc] as %fi Hfut
    ihave ⟨Hfut, %hfi⟩ := futWait_ok_rd fi _ $$ Hfut
    obtain ⟨x, rfl⟩ := hfi
    wp_apply (wp_waitFuture x _ _ wt (hfe x _)) $$ [$Hpkg $Hfut] as %err %ok Hres
    icases Hres with (%hok | ⟨%hok, Hq⟩)
    · subst hok
      wp_auto
      iright; iframe; try (ipureintro; rfl)
    subst hok
    unfold barrierQ
    icases Hq with (%hne | ⟨%hnil, Hok⟩)
    · cases err with
      | nil => exact absurd rfl hne
      | ok e =>
        wp_auto
        iright; iframe; try (ipureintro; rfl)
    subst hnil
    wp_auto
    unfold barrierOk
    icases Hok with ⟨%T, %m0, %b, %s, %st0, #HT, #Hm0, #Hst0, %hbo, Hfa⟩
    rw [Hresp]
    ihave %hmax := histLb_maxDur γ sc s (fun j hj => by have := hbo.2.2.2.2 j hj; omega) $$ Hsc
    ileft
    iframe
    isplitr; · ipureintro; rfl
    ipureintro; exact hmax
  · -- way 2: the term, a barrier of the term, VerifyLeader, the term again
    ihave ⟨#Hinv, #Hvoter⟩ := isRaft_proto $$ Hisr
    ihave #Htc := isRaft_termCell $$ Hisr
    wp_apply (wp_CurrentTerm.2 r γ i sc) $$ [$Hraft $Hinv $Hvoter $Htc $Hsc] as %t ⟨%s1, #Hs1, %hs1⟩
    wp_apply wp_Mutex_Lock $$ [$Hmu] as ⟨Hlocked, Hm⟩
    unfold apiMuInv
    icases Hm with ⟨%t0, Hbi, #Hbf⟩
    wp_auto
    wp_apply wp_Mutex_Unlock $$ [$Hmu $Hlocked Hbi]
    · inext; iexists t0; iframe Hbi; iexact Hbf
    wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗
        (⌜uint.nat t = 0⌝ ∨ barrierFact γ i fc alb (uint.nat t)) ∗
        «$res0_ptr» ↦ GoInterface.nil ∗ a_ptr ↦ a ∗ r_ptr ↦ r ∗ term_ptr ↦ t) ∨
        (⌜v = returnVal #()⌝ ∗ «$res0_ptr» ↦ GoInterface.nil ∗ a_ptr ↦ a ∗ r_ptr ↦ r)))
      with [«$res0» a r term]
    · -- a barrier of `t` recorded (or `t = 0`)
      ileft; iframe
      icases Hbf with (%h0 | #Hb)
      · ileft; ipureintro; rw [← Hif, h0]; rfl
      · iright; rw [← Hif]; iexact Hb
    · -- no barrier of `t` recorded: a barrier now, in `t`
      wp_apply (wp_Barrier r γ rc i s1 enq) $$ [$Hraft $Hisr $Hs1] as %fi Hfut
      ihave ⟨Hfut, %hfi⟩ := futWait_ok_rd fi _ $$ Hfut
      obtain ⟨x, rfl⟩ := hfi
      wp_apply (wp_waitFuture x _ _ wt (hfe x _)) $$ [$Hpkg $Hfut] as %err %ok Hres
      icases Hres with (%hok | ⟨%hok, Hq⟩)
      · subst hok
        wp_auto
        iright; iframe; try (ipureintro; rfl)
      subst hok
      unfold barrierQ
      icases Hq with (%hne | ⟨%hnil, Hok⟩)
      · cases err with
        | nil => exact absurd rfl hne
        | ok e =>
          wp_auto
          iright; iframe; try (ipureintro; rfl)
      subst hnil
      wp_auto
      unfold barrierOk
      icases Hok with ⟨%T, %m0, %b, %sb, %st0, #HT, #Hm0, #Hst0, %hbo, Hfa⟩
      rw [Hresp]
      ihave #Hfa := Hfa
      wp_apply (wp_CurrentTerm.2 r γ i st0) $$ [$Hraft $Hinv $Hvoter $Htc $Hst0] as %t2 ⟨%s2, #Hs2, %hs2⟩
      wp_if_destruct
      rotate_left
      · -- the term moved: no read
        iright; iframe; try (ipureintro; rfl)
      subst t2
      -- the barrier's term is `t`
      have hT : T = uint.nat t := by
        have h1 := hbo.1.2.1 i
        have h3 := hs2.1.2.1 i
        rw [hs1.2, hbo.2.1] at h1
        rw [hbo.2.1, hs2.2] at h3
        omega
      subst hT
      wp_apply wp_Mutex_Lock $$ [$Hmu] as ⟨Hlocked, ⟨%t1, Hbi, -⟩⟩
      try wp_auto
      ihave #Hbf' : barrierFact γ i fc alb (uint.nat t) $$ []
      · unfold barrierFact; iexists m0, sb; iframe #; ipureintro; omega
      wp_apply wp_Mutex_Unlock $$ [$Hmu $Hlocked Hbi]
      · inext; iexists t; iframe Hbi; iright; iexact Hbf'
      ileft; iframe
      isplitr; · ipureintro; rfl
      iright; iexact Hbf'
    · iintro Hv
      icases Hv with (⟨%hv, #HR, H0, a, r, term⟩ | ⟨%hv, H0, a, r⟩)
      · subst hv
        wp_auto
        wp_apply (wp_VerifyLeader r γ rc i s1) $$ [$Hraft $Hisr $Hs1] as %fi Hfut
        ihave ⟨Hfut, %hfi⟩ := futWait_ok_rd fi _ $$ Hfut
        obtain ⟨x, rfl⟩ := hfi
        wp_apply (wp_waitFuture x _ _ wt (hfe x _)) $$ [$Hpkg $Hfut] as %err %ok Hres
        icases Hres with (%hok | ⟨%hok, Hq⟩)
        · subst hok
          wp_auto
          iright; iframe; try (ipureintro; rfl)
        subst hok
        unfold verifyQ
        icases Hq with (%hne | ⟨%hnil, Hok⟩)
        · cases err with
          | nil => exact absurd rfl hne
          | ok e =>
            wp_auto
            iright; iframe; try (ipureintro; rfl)
        subst hnil
        wp_auto
        unfold verifyOk
        icases Hok with ⟨%sv, Hvi, Hfav⟩
        unfold verifyItem
        icases Hvi with ⟨%T', %n0', %st', #HT', #Hn0', #Hst', %hvi⟩
        iapply fupd_wp
        imod leaderIs_pos γ ⊤ (by solve_ndisj) T' i $$ [$Hinv $HT'] with %hTpos
        imodintro
        rw [Hresp]
        ihave #Hfav := Hfav
        wp_apply (wp_CurrentTerm.2 r γ i st') $$ [$Hraft $Hinv $Hvoter $Htc $Hst'] as %t3 ⟨%s3, #Hs3, %hs3⟩
        wp_if_destruct
        rotate_left
        · iright; iframe; try (ipureintro; rfl)
        subst t3
        -- the verify's term is `t`
        have hT : T' = uint.nat t := by
          have h1 := hvi.1.2.1 i
          have h3 := hs3.1.2.1 i
          rw [hs1.2, hvi.2.1] at h1
          rw [hvi.2.1, hs3.2] at h3
          omega
        subst hT
        unfold barrierFact
        icases HR with (%h0 | ⟨%n0b, %sb, #HTb, #Hn0b, %hn0b, #Hfab⟩)
        · exfalso; omega
        ihave %hn := len0Is_agree γ (uint.nat t) n0b n0' $$ [Hn0b Hn0']
        · iframe #
        subst hn
        have hdur : ∀ j ∈ γ.srvs, sc.dur j ≤ Max.max sb sv := by
          intro j hj
          have h1 := hs1.1.2.2.1 j
          have := Nat.le_max_left sb sv
          have := Nat.le_max_right sb sv
          rcases hvi.2.2 j hj with h | h <;> omega
        ihave %hmax := histLb_maxDur γ sc (Max.max sb sv) hdur $$ Hsc
        ileft; iframe
        by_cases hle : sb ≤ sv
        · iexists sv
          iframe #
          ipureintro; rw [Nat.max_eq_right hle] at hmax; exact hmax
        · iexists sb
          iframe #
          ipureintro; rw [Nat.max_eq_left (by omega)] at hmax; exact hmax
      · subst hv
        wp_auto
        iright; iframe; try (ipureintro; rfl)
  · -- the read: the store's prefix, at least what the FSM had applied at `s`
    iintro Hv
    icases Hv with (⟨%hv, ⟨%s, #Hfa, %hs⟩, H0, a, r⟩ | ⟨%hv, H0, a, r⟩)
    · subst hv
      wp_auto
      icases github_com.hashicorp.raft.fsmAt_elim γ _ i s $$ Hfa with ⟨%k0, %rr, #Hrr, %hk, #Hnc, #Hd⟩
      ihave #Hk0 : (⌜k0 = 0⌝ ∨ appliedLb alb k0 : IProp GF) $$ []
      · icases Hrr with (%h0 | #Hrp)
        · ileft; ipureintro; exact h0
        · iright
          unfold respP
          icases Hrp with ⟨%es, -, -, -, #Ha⟩
          iexact Ha
      iapply wp_fupd
      wp_apply (lc := 2) (wp_read γ fc alb i fsm k0) $$ [$Hpkg $Hst $Hk0] as %res ⟨%es, #Hlb, %hes⟩
      obtain ⟨hl, hk0, rfl⟩ := hes
      have hcl : lastCmd es ∧ k0 ≤ es.length ∧ n0 ≤ s := ⟨hl, hk0, by omega⟩
      iunfold rdClaim at Hcl
      imod Hcl $$ %es %k0 %s %hcl Hnc Hlb Hlc1 Hlc2 with HΨ
      imodintro
      iapply HΦ
      iexists _
      iframe Hrep
      iintro -
      iexact HΨ
    · subst hv
      wp_auto
      iapply HΦ
      iexists _
      iframe Hrep
      iintro %h
      exfalso
      simp [Perennial.zero_val] at h
