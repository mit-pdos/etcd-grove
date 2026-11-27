/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/deferError__Error.lean (241f27e).
-/
/-
The proof of `raft.(*deferError).Error`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.deferError__Error

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

/-- A select case receiving from a bag channel (local copy of `leaderLoop`'s). -/
theorem de_bag_recv_clause {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [Pos.Countable V]
    {t : go.GoType} [IntoValTyped (GF := GF) V t]
    (ch : Loc) (γc : ChanNames) (P : V → IProp GF) (h : Expr) (Ψ : val → IProp GF) :
    £ 1 ∗ £ 1 ∗ isChanBag γc ch P ∗ ▷ (∀ v, P v -∗ WP (App h (Val (PairV #v #true))) {{ Ψ }}) ⊢
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) h) Ψ := by
  iintro ⟨Hl1, Hl2, #Hb, HΦ⟩
  simp only [chan.blockingClausePre]
  iexists V, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
  isplitr; · ipureintro; rfl
  isplitr; · iapply is_bag_is_chan γc ch P $$ Hb
  iapply bag_recv_au γc ch P (fun v ok => iprop(WP (App h (Val (PairV #v #ok))) {{ Ψ }}))
    $$ [Hl1 Hl2] Hb HΦ
  iframe

/-- A select case receiving from a channel that is never sent on (local copy of `leaderLoop`'s). -/
theorem de_dead_recv_clause {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [Pos.Countable V]
    {t : go.GoType} [IntoValTyped (GF := GF) V t]
    (ch : Loc) (γc : ChanNames) (h : Expr) (Ψ : val → IProp GF) :
    £ 1 ∗ £ 1 ∗ isChanBag (V := V) γc ch (fun _ => iprop(False)) ⊢
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) h) Ψ := by
  iintro ⟨Hl1, Hl2, #Hb⟩
  iapply de_bag_recv_clause ch γc _ h Ψ
  iframe; iframe #
  inext; iintro %v Hf; iexfalso; iexact Hf

theorem github_com.hashicorp.raft.deferError.Error.wp_lf (f : Loc) (Q : GoInterface → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ deferWait (f.[logFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType logFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }} := by
  wp_start as Hw
  wp_method_call
  wp_call
  unfold deferWait
  icases Hw with ⟨%ch, %γe, #Hch, %Hne, #Hspsc, Hcons, Herr, %sc, #Hsd, #Hscd⟩
  wp_auto_lc 4
  rw [show decide (ch = chan.nil) = false from decide_eq_false Hne]
  wp_auto
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, ch, γe.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold isSpsc; icases Hspsc with ⟨$, -⟩
    iapply spsc_rcv_au $$ Hspsc [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok Hv
    cases ok
    · -- closed without a value: impossible, `respond` sends before closing (close predicate)
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨%Hc, -⟩
      exact absurd rfl Hc
    · simp only [↓reduceIte]
      icases Hv with ⟨⟨-, HQ⟩, -⟩
      wp_auto
      iapply HΦ $$ HQ
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `ShutdownCh`: nil, or never sent on and never closed (stage 3: raft's own futures)
    icases Hscd with (%Hnil | #Hdead)
    · iright
      subst Hnil
      iapply chan.nilClausePre_recv Unit _ _ rfl
    · ileft
      iunfold deadChan at Hdead
      icases Hdead with ⟨%γsc, #Hdead⟩
      iapply de_dead_recv_clause sc γsc
      iframe; iframe #
  iapply BigAndL.bigAndL_nil.2
  itrivial

theorem github_com.hashicorp.raft.deferError.Error.wp_vf (f : Loc) (Q : GoInterface → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ deferWait (f.[verifyFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType verifyFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }} := by
  wp_start as Hw
  wp_method_call
  wp_call
  unfold deferWait
  icases Hw with ⟨%ch, %γe, #Hch, %Hne, #Hspsc, Hcons, Herr, %sc, #Hsd, #Hscd⟩
  wp_auto_lc 4
  rw [show decide (ch = chan.nil) = false from decide_eq_false Hne]
  wp_auto
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, ch, γe.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold isSpsc; icases Hspsc with ⟨$, -⟩
    iapply spsc_rcv_au $$ Hspsc [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok Hv
    cases ok
    · -- closed without a value: impossible, `respond` sends before closing (close predicate)
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨%Hc, -⟩
      exact absurd rfl Hc
    · simp only [↓reduceIte]
      icases Hv with ⟨⟨-, HQ⟩, -⟩
      wp_auto
      iapply HΦ $$ HQ
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `ShutdownCh`: nil, or never sent on and never closed (stage 3: raft's own futures)
    icases Hscd with (%Hnil | #Hdead)
    · iright
      subst Hnil
      iapply chan.nilClausePre_recv Unit _ _ rfl
    · ileft
      iunfold deadChan at Hdead
      icases Hdead with ⟨%γsc, #Hdead⟩
      iapply de_dead_recv_clause sc γsc
      iframe; iframe #
  iapply BigAndL.bigAndL_nil.2
  itrivial

theorem github_com.hashicorp.raft.deferError.Error.wp_ltf (f : Loc) (Q : GoInterface → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ deferWait (f.[leadershipTransferFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType leadershipTransferFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }} := by
  wp_start as Hw
  wp_method_call
  wp_call
  unfold deferWait
  icases Hw with ⟨%ch, %γe, #Hch, %Hne, #Hspsc, Hcons, Herr, %sc, #Hsd, #Hscd⟩
  wp_auto_lc 4
  rw [show decide (ch = chan.nil) = false from decide_eq_false Hne]
  wp_auto
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, ch, γe.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold isSpsc; icases Hspsc with ⟨$, -⟩
    iapply spsc_rcv_au $$ Hspsc [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok Hv
    cases ok
    · -- closed without a value: impossible, `respond` sends before closing (close predicate)
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨%Hc, -⟩
      exact absurd rfl Hc
    · simp only [↓reduceIte]
      icases Hv with ⟨⟨-, HQ⟩, -⟩
      wp_auto
      iapply HΦ $$ HQ
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `ShutdownCh`: nil, or never sent on and never closed (stage 3: raft's own futures)
    icases Hscd with (%Hnil | #Hdead)
    · iright
      subst Hnil
      iapply chan.nilClausePre_recv Unit _ _ rfl
    · ileft
      iunfold deadChan at Hdead
      icases Hdead with ⟨%γsc, #Hdead⟩
      iapply de_dead_recv_clause sc γsc
      iframe; iframe #
  iapply BigAndL.bigAndL_nil.2
  itrivial

theorem github_com.hashicorp.raft.deferError.Error.wp_usf (f : Loc) (Q : GoInterface → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ deferWait (f.[userSnapshotFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType userSnapshotFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }} := by
  wp_start as Hw
  wp_method_call
  wp_call
  unfold deferWait
  icases Hw with ⟨%ch, %γe, #Hch, %Hne, #Hspsc, Hcons, Herr, %sc, #Hsd, #Hscd⟩
  wp_auto_lc 4
  rw [show decide (ch = chan.nil) = false from decide_eq_false Hne]
  wp_auto
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, ch, γe.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold isSpsc; icases Hspsc with ⟨$, -⟩
    iapply spsc_rcv_au $$ Hspsc [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok Hv
    cases ok
    · -- closed without a value: impossible, `respond` sends before closing (close predicate)
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨%Hc, -⟩
      exact absurd rfl Hc
    · simp only [↓reduceIte]
      icases Hv with ⟨⟨-, HQ⟩, -⟩
      wp_auto
      iapply HΦ $$ HQ
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `ShutdownCh`: nil, or never sent on and never closed (stage 3: raft's own futures)
    icases Hscd with (%Hnil | #Hdead)
    · iright
      subst Hnil
      iapply chan.nilClausePre_recv Unit _ _ rfl
    · ileft
      iunfold deadChan at Hdead
      icases Hdead with ⟨%γsc, #Hdead⟩
      iapply de_dead_recv_clause sc γsc
      iframe; iframe #
  iapply BigAndL.bigAndL_nil.2
  itrivial

theorem github_com.hashicorp.raft.deferError.Error.wp_d (f : Loc) (Q : GoInterface → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ deferWait (f) Q }}
    (App (Val (f @!! go.GoType.PointerType deferError.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }} := by
  wp_start as Hw
  unfold deferWait
  icases Hw with ⟨%ch, %γe, #Hch, %Hne, #Hspsc, Hcons, Herr, %sc, #Hsd, #Hscd⟩
  wp_auto_lc 4
  rw [show decide (ch = chan.nil) = false from decide_eq_false Hne]
  wp_auto
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, ch, γe.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold isSpsc; icases Hspsc with ⟨$, -⟩
    iapply spsc_rcv_au $$ Hspsc [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok Hv
    cases ok
    · -- closed without a value: impossible, `respond` sends before closing (close predicate)
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨%Hc, -⟩
      exact absurd rfl Hc
    · simp only [↓reduceIte]
      icases Hv with ⟨⟨-, HQ⟩, -⟩
      wp_auto
      iapply HΦ $$ HQ
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `ShutdownCh`: nil, or never sent on and never closed (stage 3: raft's own futures)
    icases Hscd with (%Hnil | #Hdead)
    · iright
      subst Hnil
      iapply chan.nilClausePre_recv Unit _ _ rfl
    · ileft
      iunfold deadChan at Hdead
      icases Hdead with ⟨%γsc, #Hdead⟩
      iapply de_dead_recv_clause sc γsc
      iframe; iframe #
  iapply BigAndL.bigAndL_nil.2
  itrivial

/-- (stage 4) Through `*configurationChangeFuture` (promoted through its embedded `logFuture`). -/
theorem github_com.hashicorp.raft.deferError.Error.wp_ccf (f : Loc) (Q : GoInterface → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     deferWait ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"]) Q }}
    (App (Val (f @!! go.GoType.PointerType configurationChangeFuture.ty @!! go!"Error")) (Val #()))
  {{ (err : GoInterface), RET #err; Q err }} := by
  wp_start as Hw
  wp_method_call
  wp_call
  wp_method_call
  wp_call
  unfold deferWait
  icases Hw with ⟨%ch, %γe, #Hch, %Hne, #Hspsc, Hcons, Herr, %sc, #Hsd, #Hscd⟩
  wp_auto_lc 4
  rw [show decide (ch = chan.nil) = false from decide_eq_false Hne]
  wp_auto
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, ch, γe.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold isSpsc; icases Hspsc with ⟨$, -⟩
    iapply spsc_rcv_au $$ Hspsc [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok Hv
    cases ok
    · -- closed without a value: impossible, `respond` sends before closing (close predicate)
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨%Hc, -⟩
      exact absurd rfl Hc
    · simp only [↓reduceIte]
      icases Hv with ⟨⟨-, HQ⟩, -⟩
      wp_auto
      iapply HΦ $$ HQ
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `ShutdownCh`: nil, or never sent on and never closed (stage 3: raft's own futures)
    icases Hscd with (%Hnil | #Hdead)
    · iright
      subst Hnil
      iapply chan.nilClausePre_recv Unit _ _ rfl
    · ileft
      iunfold deadChan at Hdead
      icases Hdead with ⟨%γsc, #Hdead⟩
      iapply de_dead_recv_clause sc γsc
      iframe; iframe #
  iapply BigAndL.bigAndL_nil.2
  itrivial


theorem github_com.hashicorp.raft.deferError.Error.wp_proof :
    github_com.hashicorp.raft.deferError.Error.spec (GF := GF) (hG := hG) :=
  ⟨github_com.hashicorp.raft.deferError.Error.wp_lf, github_com.hashicorp.raft.deferError.Error.wp_vf,
    github_com.hashicorp.raft.deferError.Error.wp_ltf, github_com.hashicorp.raft.deferError.Error.wp_usf,
    github_com.hashicorp.raft.deferError.Error.wp_ccf, github_com.hashicorp.raft.deferError.Error.wp_d⟩

end proof

end Perennial
