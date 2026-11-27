/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__initiateLeadershipTransfer.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).initiateLeadershipTransfer` (stage 2; its spec is API-internal:
`LeadershipTransfer` and `LeadershipTransferToServer` call it).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__initiateLeadershipTransfer
public import Perennial.Spec.fmt.Errorf

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

theorem github_com.hashicorp.raft.Raft.initiateLeadershipTransfer.wp_proof
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.initiateLeadershipTransfer.spec (GF := GF) (hG := hG) := by
  intro r γ rc i idp ap
  wp_start as ⟨#Hr, Htgt⟩
  wp_auto
  ihave Hch := isRaft_chans r γ rc i $$ Hr
  unfold raftChans deadField deadChan
  icases Hch with ⟨-, -, ⟨%lch, #Hlch, %γt, #Hbag⟩, -, -, -, -, -, -, ⟨%sdCh, #HsdCh, %γsd, #Hsd⟩, -⟩
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, #HlocalID, -⟩
  irename «$r0» => Hf
  generalize «$r0_ptr» = f at *
  iStructNamed Hf
  try simp only [zeroValDef] at *
  iStructNamed deferError
  wp_apply (lc := 2) futProof.wp_ltf_init f (fun _ => iprop(True)) null $$ [$errCh]
    as ⟨%ch, %γe, %Hne, HerrCh, #Hspsc, Hprod, Hcons⟩
  ipersist HerrCh
  ipersist ShutdownCh
  icases Htgt with (⟨%Hid, %Ha⟩ | ⟨%j, #Hidp, #Hap, #Hvj⟩)
  · -- no target
    subst Hid Ha
    wp_auto
    ihave HP : ltfP γ i f $$ [ID Address responded Hprod]
    · unfold ltfP
      iexists null, null
      iframe
      isplitr
      · ileft; ipureintro; exact ⟨rfl, rfl⟩
      unfold deferResp
      iexists ch
      iframe #
      iright
      iframe
      ipureintro; exact Hne
    -- the non-blocking select: the send on leadershipTransferCh, shutdownCh (never), default
    wp_apply_core chan.wp_select_nonblocking
    isplit
    · iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.nonblockingClausePre]
        iexists Loc, inferInstance, inferInstance,
        (inferInstance : IntoValTyped Loc (go.GoType.PointerType leadershipTransferFuture.ty)),
        inferInstance, lch, γt, f
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        isplitr
        · iapply is_bag_is_chan $$ Hbag
        unfold nonblockingSendAu
        isplit
        · iapply futProof.bag_nb_send_au (t := go.GoType.PointerType leadershipTransferFuture.ty) $$ Hlc1 Hbag HP
          inext
          wp_auto
          iapply HΦ
          unfold futWait
          iright; iright; iright; ileft
          iexists f
          isplitr
          · ipureintro; rfl
          unfold deferWait
          iexists ch, γe
          iframe
          iframe #
          rw [show (chan.nil : GoChan) = null from rfl]
          iframe #
          isplitr; · ipureintro; exact Hne
          ileft; ipureintro; rfl
        · itrivial
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.nonblockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sdCh, γsd
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply is_bag_is_chan $$ Hsd
        unfold nonblockingRecvAu
        isplit
        · iapply futProof.bag_nb_recv_au $$ Hlc2 Hsd
          inext
          iintro %v Hf
          iexfalso; iexact Hf
        · itrivial
      iapply BigAndL.bigAndL_nil.2
      itrivial
    · -- default: enqueue timeout
      icases isRaftErr_of_init .enqueueTimeout $$ Hpkg with ⟨%e, #He⟩
      ihave #Hg : (globalAddr ErrEnqueueTimeout ↦□ e : IProp GF) $$ []
      · have h := isRaftErr_global (GF := GF) .enqueueTimeout e
        rw [show RaftErr.enqueueTimeout.var = ErrEnqueueTimeout from rfl] at h
        iapply h $$ He
      wp_auto
      iapply HΦ
      unfold futWait
      ileft
      iexists e
      isplitr
      · ipureintro; rfl
      itrivial
  · -- a target `j`
    ihave %Hidn := typedPointsto_not_null idp _ _ $$ Hidp
    simp only [decide_eq_false Hidn, Bool.not_false]
    wp_auto
    by_cases hj : j = i
    · -- to itself: answered at once (`fmt.Errorf`)
      subst hj
      simp only [decide_true]
      wp_auto
      ihave #HfmtS : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
      · first | iPkgInit | iframe
      wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) $$ [$HfmtS] as %e -
      · isplitr
        · iapply ownSlice_nil
        · iapply (_root_.Perennial.fmt.argsOk_of_argsWf (by intro ii h; simp at h))
      wp_apply futProof.wp_ltf_respond f (fun _ => iprop(True)) (GoInterface.ok e) $$ [responded Hprod] as Hdone
      · ileft
        isplitl
        · unfold deferResp
          iexists ch
          iframe #
          iright
          iframe
          ipureintro; exact Hne
        · itrivial
      iapply HΦ
      unfold futWait
      iright; iright; iright; ileft
      iexists f
      isplitr
      · ipureintro; rfl
      unfold deferWait
      iexists ch, γe
      iframe
      iframe #
      rw [show (chan.nil : GoChan) = null from rfl]
      iframe #
      isplitr; · ipureintro; exact Hne
      ileft; ipureintro; rfl
    · simp only [decide_eq_false hj]
      wp_auto
      ihave HP : ltfP γ i f $$ [ID Address responded Hprod]
      · unfold ltfP
        iexists idp, ap
        iframe
        isplitr
        · iright; iexists j; iframe #; ipureintro; exact hj
        unfold deferResp
        iexists ch
        iframe #
        iright
        iframe
        ipureintro; exact Hne
      -- the non-blocking select: the send on leadershipTransferCh, shutdownCh (never), default
      wp_apply_core chan.wp_select_nonblocking
      isplit
      · iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.nonblockingClausePre]
          iexists Loc, inferInstance, inferInstance,
          (inferInstance : IntoValTyped Loc (go.GoType.PointerType leadershipTransferFuture.ty)),
          inferInstance, lch, γt, f
          isplitr
          · ipureintro; exact ⟨rfl, rfl⟩
          isplitr
          · iapply is_bag_is_chan $$ Hbag
          unfold nonblockingSendAu
          isplit
          · iapply futProof.bag_nb_send_au (t := go.GoType.PointerType leadershipTransferFuture.ty) $$ Hlc1 Hbag HP
            inext
            wp_auto
            iapply HΦ
            unfold futWait
            iright; iright; iright; ileft
            iexists f
            isplitr
            · ipureintro; rfl
            unfold deferWait
            iexists ch, γe
            iframe
            iframe #
            rw [show (chan.nil : GoChan) = null from rfl]
            iframe #
            isplitr; · ipureintro; exact Hne
            ileft; ipureintro; rfl
          · itrivial
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.nonblockingClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sdCh, γsd
          isplitr
          · ipureintro; rfl
          isplitr
          · iapply is_bag_is_chan $$ Hsd
          unfold nonblockingRecvAu
          isplit
          · iapply futProof.bag_nb_recv_au $$ Hlc2 Hsd
            inext
            iintro %v Hf
            iexfalso; iexact Hf
          · itrivial
        iapply BigAndL.bigAndL_nil.2
        itrivial
      · -- default: enqueue timeout
        icases isRaftErr_of_init .enqueueTimeout $$ Hpkg with ⟨%e, #He⟩
        ihave #Hg : (globalAddr ErrEnqueueTimeout ↦□ e : IProp GF) $$ []
        · have h := isRaftErr_global (GF := GF) .enqueueTimeout e
          rw [show RaftErr.enqueueTimeout.var = ErrEnqueueTimeout from rfl] at h
          iapply h $$ He
        wp_auto
        iapply HΦ
        unfold futWait
        ileft
        iexists e
        isplitr
        · ipureintro; rfl
        itrivial

end proof

end Perennial
