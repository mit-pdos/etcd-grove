/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/main/Respond.lean (241f27e).
-/
/-
(stage 2, MAIN-F helper) `respond` on a `*verifyFuture` and on a `*leadershipTransferFuture`
(their embedded `deferError`'s): the same contract as `deferError.respond.spec` (which is stated for
`*logFuture`), for the main goroutine's rejections (`runFollower`, `runCandidate`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond

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

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.wp_verifyFuture_respond (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
        ((deferResp (f.[verifyFuture, go!"deferError"]) Q ∗ Q err) ∨ deferDone (f.[verifyFuture, go!"deferError"])) }}
      (App (Val (f @!! go.GoType.PointerType verifyFuture.ty @!! go!"respond")) (Val #err))
    {{ RET #(); deferDone (f.[verifyFuture, go!"deferError"]) }} := by
  wp_start as Hpre
  wp_method_call
  wp_call
  unfold deferDone
  icases Hpre with (⟨Hresp, HQ⟩ | Hdone)
  · unfold deferResp
    icases Hresp with ⟨%ch, #Hch, (%Hnil | ⟨%γe, %Hne, #Hspsc, Hprod, Hr⟩)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      rw [show decide (ch = chan.nil) = false from decide_eq_false Hne]
      wp_auto
      wp_apply (wp_spsc_send γe ch _ _ [] err) $$ [$Hspsc $Hprod HQ] as Hprod
      · iframe; ipureintro; rfl
      wp_apply (wp_spsc_close γe ch _ _ ([] ++ [err])) $$ [$Hspsc $Hprod]
      · ipureintro; simp
      iapply HΦ
      iexists ch; iframe #; iright; iframe
  · icases Hdone with ⟨%ch, #Hch, (%Hnil | Hr)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      wp_if_destruct
      · iapply HΦ
        iexists _; iframe #; ileft; ipureintro; rfl
      · iapply HΦ
        iexists ch; iframe #; iright; iframe

theorem github_com.hashicorp.raft.wp_ltFuture_respond (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
        ((deferResp (f.[leadershipTransferFuture, go!"deferError"]) Q ∗ Q err) ∨ deferDone (f.[leadershipTransferFuture, go!"deferError"])) }}
      (App (Val (f @!! go.GoType.PointerType leadershipTransferFuture.ty @!! go!"respond")) (Val #err))
    {{ RET #(); deferDone (f.[leadershipTransferFuture, go!"deferError"]) }} := by
  wp_start as Hpre
  wp_method_call
  wp_call
  unfold deferDone
  icases Hpre with (⟨Hresp, HQ⟩ | Hdone)
  · unfold deferResp
    icases Hresp with ⟨%ch, #Hch, (%Hnil | ⟨%γe, %Hne, #Hspsc, Hprod, Hr⟩)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      rw [show decide (ch = chan.nil) = false from decide_eq_false Hne]
      wp_auto
      wp_apply (wp_spsc_send γe ch _ _ [] err) $$ [$Hspsc $Hprod HQ] as Hprod
      · iframe; ipureintro; rfl
      wp_apply (wp_spsc_close γe ch _ _ ([] ++ [err])) $$ [$Hspsc $Hprod]
      · ipureintro; simp
      iapply HΦ
      iexists ch; iframe #; iright; iframe
  · icases Hdone with ⟨%ch, #Hch, (%Hnil | Hr)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      wp_if_destruct
      · iapply HΦ
        iexists _; iframe #; ileft; ipureintro; rfl
      · iapply HΦ
        iexists ch; iframe #; iright; iframe

/-- **A voted verify future received back by the main goroutine** (its back token): the registry
gives its responder state (pending, with some client snapshot, or already answered); once answered
(`deferDone`) the registry is whole again (the future stays live, answered; its token is spent). -/
theorem github_com.hashicorp.raft.registry_voted (γ : GNames) (rc : RCtx GF) (i : SID) (v : Loc) :
    verifyRegistry γ rc i ∗ backTok rc v ⊢
      ((∃ sc : Snap, deferResp (v.[verifyFuture, go!"deferError"]) (verifyQ γ rc i sc)) ∨
        deferDone (v.[verifyFuture, go!"deferError"])) ∗
      (deferDone (v.[verifyFuture, go!"deferError"]) -∗ verifyRegistry γ rc i) := by
  unfold verifyRegistry backTok
  iintro ⟨⟨%V, %R, %Live, %NMs, HV, HR, HL, HN, %Hinc, Hq, HLm⟩, Hb⟩
  ihave %hl := ghost_map_lookup $$ HL Hb
  ihave ⟨Hv, Hcl⟩ := (BigSepM.bigSepM_lookup_acc (Φ := fun v (_u : Unit) => iprop(∃ (T : Nat) (sv : Snap),
      ⌜R.lookup v = some (T, sv)⌝ ∗ vregState γ rc i v sv ((NMs.lookup v).isSome))) hl).1 $$ HLm
  icases Hv with ⟨%T, %sv, %HR', Hst⟩
  unfold vregState
  isplitl [Hst]
  · icases Hst with (⟨%sc, -, -, Hd⟩ | Hd)
    · ileft; iexists sc; iexact Hd
    · iright; iexact Hd
  iintro Hd
  iexists V, R, Live, NMs
  iframe
  isplitr
  · ipureintro; exact Hinc
  iapply Hcl
  iexists T, sv
  isplitr
  · ipureintro; exact HR'
  iright; iexact Hd

/-- **A rejection of a `verifyCh` element** (`v.respond(err)`, `err` an error: the follower's and
candidate's `ErrNotLeader`): a fresh future is answered with its own responder side; a voted one
through the registry. -/
theorem github_com.hashicorp.raft.wp_verify_reject (γ : GNames) (rc : RCtx GF) (i : SID) (vch v : Loc)
    (err : GoInterface) (herr : err ≠ interface.nil) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ verifyRegistry γ rc i ∗
        verifyP γ rc i vch v }}
      (App (Val (v @!! go.GoType.PointerType verifyFuture.ty @!! go!"respond")) (Val #err))
    {{ RET #(); verifyRegistry γ rc i }} := by
  wp_start_folded as ⟨Hreg, Hv⟩
  unfold verifyP
  icases Hv with (Hn | Hvt)
  · unfold verifyNew
    icases Hn with ⟨%sc, -, -, -, -, -, Hde⟩
    wp_apply (wp_verifyFuture_respond v (verifyQ γ rc i sc) err) $$ [Hde] as -
    · ileft; iframe; unfold verifyQ; ileft; ipureintro; exact herr
    iapply HΦ; iexact Hreg
  · unfold verifyVoted
    icases Hvt with ⟨%T, %sv, %L, %n, %q, -, Hb, -, -, -⟩
    icases registry_voted γ rc i v $$ [$Hreg $Hb] with ⟨Hd, Hcl⟩
    icases Hd with (⟨%sc, Hd⟩ | Hd)
    · wp_apply (wp_verifyFuture_respond v (verifyQ γ rc i sc) err) $$ [Hd] as Hd
      · ileft; iframe; unfold verifyQ; ileft; ipureintro; exact herr
      iapply HΦ; iapply Hcl $$ Hd
    · wp_apply (wp_verifyFuture_respond v (fun _ => iprop(True)) err) $$ [Hd] as Hd
      · iright; iexact Hd
      iapply HΦ; iapply Hcl $$ Hd

/-- **A rejection of a `leadershipTransferCh` element** (`f.respond(err)`). -/
theorem github_com.hashicorp.raft.wp_lt_reject (γ : GNames) (i : SID) (f : Loc) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ ltfP γ i f }}
      (App (Val (f @!! go.GoType.PointerType leadershipTransferFuture.ty @!! go!"respond")) (Val #err))
    {{ RET #(); True }} := by
  wp_start_folded as Hf
  unfold ltfP
  icases Hf with ⟨%idp, %ap, -, -, -, Hde⟩
  wp_apply (wp_ltFuture_respond f (fun _ => iprop(True)) err) $$ [Hde] as -
  · ileft; iframe
  iapply HΦ; itrivial

/-- The main goroutine's registry of verify futures, out of `mainOwnAt`. -/
theorem github_com.hashicorp.raft.mainOwnAt_registry (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID)
    (s : SState) (st : w32) :
    mainOwnAt r γ rc i s st ⊢ verifyRegistry γ rc i ∗ (verifyRegistry γ rc i -∗ mainOwnAt r γ rc i s st) := by
  unfold mainOwnAt
  iintro ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, H1, H2, H3, H4, H5, Hst, Hl, Hp, Hv, H8⟩
  iframe Hv
  iintro Hv
  iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, c
  iframe

end proof

end Perennial
