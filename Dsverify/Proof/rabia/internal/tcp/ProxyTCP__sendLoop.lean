/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/ProxyTCP__sendLoop.lean`,
run `rabia-r1wake-1`, onto `Net/`'s connections and the revised bufio: the writer is `wrOwn`.)

The proof of `rabia/internal/tcp.(*ProxyTCP).sendLoop`: the send routine of one accepted
connection writes the replies of its channel (`repP`) to its client (`proxyQ`).
-/
module

public import Dsverify.Proof.rabia.internal.tcp.ProxyLemmas
public import Perennial.Proof.sync

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
  rabia.internal.message rabia.internal.config

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [package_sem : rabia.internal.tcp.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions]
variable [net.Assumptions] [go.BasicIntoValInj]
variable [msg_sem : rabia.internal.message.Assumptions] [sync.Assumptions]

set_option goose.wp.extras true

theorem wp_ProxyTCP_sendLoop (D : TcpDeps (GF := GF)) (γ : Names) (k : Nat) (p : Loc) (c : Nat) (ch : GoChan)
    (γch : ChanNames) (bw : Loc) (cid : Nat) (done : GoChan) (wg : Loc) (hc : c < nC) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗
      p.[ProxyTCP, go!"Done"] ↦□ done ∗ doneChan done ∗
      p.[ProxyTCP, go!"Wg"] ↦□ wg ∗ wgTok wg ∗ isChanBag γch ch (repP γ c) ∗
      wrOwn bw cid true (proxyQ γ k) [] [] interface.nil ∗
      sentLb (Gg := hG.goose_globalGS) cid false (hsBytes c) }}
    (App (App (Val (p @!! go.GoType.PointerType ProxyTCP.ty @!! go!"sendLoop")) (Val #ch)) (Val #bw))
  {{ RET #(); True }} := by
  wp_start as ⟨#HD, #Hdone, #HWg, Htok, #Hbag, Hw, #Hs⟩
  wp_apply wp_with_defer as %defer Hdefer
  unfold doneChan
  icases Hdone with ⟨%γd, #Hdbag⟩
  ihave HI : (∃ (rs : List CmdV), "Hw" ∷ wrOwn bw cid true (proxyQ γ k) (frames (rs.map encCmd)) [] interface.nil ∗
      "%Hrs" ∷ ⌜∀ r ∈ rs, (encCmd r).length < 2 ^ 32⌝ ∗
      "#Hreps" ∷ [∗list] q ∈ rs, repOk γ c q : IProp GF) $$ [Hw]
  · iexists []
    simp only [List.map_nil, frames_nil]
    iframe
    isplitr
    · ipureintro; simp
    iapply BigSepL.bigSepL_nil.2; iempintro
  wp_for_core
  iNamed HI
  wp_auto_lc 1
  irename Hlc1 => Hlc2
  cleanup_bool_decide
  wp_auto_lc 1
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, done, γd
    isplitr
    · ipureintro; rfl
    ihave #Hdch := is_bag_is_chan _ _ _ $$ Hdbag
    iframe Hdch
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hdbag
    inext
    iintro %v Hv
    unfold doneP
    iexfalso; iexact Hv
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists Command, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
    isplitr
    · ipureintro; rfl
    ihave #Hch := is_bag_is_chan _ _ _ $$ Hbag
    iframe Hch
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %v Hv
    unfold repP
    icases Hv with ⟨%q, #Hrep, #Hq⟩
    wp_auto
    ipersist c
    ihave #Hq' := Hq
    iunfold repOk at Hq'
    icases Hq' with ⟨%s0, %id, %rs0, %bc0, %j0, %res, %cmds, %cmd, %Hqc, -⟩
    have hcl : q.commands.length ≤ 1 := by rw [Hqc.2.1]; simp
    have hW : frames (rs.map encCmd) ++ [] ++ model.frame (encCmd q) = frames ((rs ++ [q]).map encCmd) := by
      simp [frames_append, frames_cons, frames_nil]
    ihave #Hpkgm : (isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message) $$ []
    · iPkgInit
    wp_apply wp_cmdMarshalWriteFlush D c_ptr v q bw cid true (proxyQ γ k) _ [] _
      $$ [$Hpkgm $c $Hrep $Hw] as %e ⟨%sent', %pend', %Hsw, Hw⟩
    · isplitr
      · ipureintro; exact hcl
      imodintro
      iintro %Hlen
      rw [hW]
      unfold proxyQ
      iright
      iexists c, rs ++ [q]
      iframe Hs
      isplitr
      · ipureintro
        refine ⟨hc, List.prefix_refl _, ?_⟩
        intro r hr
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact Hrs r hr
        · exact Hlen
      iapply BigSepL.bigSepL_snoc.2
      iframe #
    rcases e with ei | _
    · wp_auto
      wp_for_post
      wp_apply wp_wgDone wg $$ [$Htok]
      iapply HΦ
      itrivial
    · obtain ⟨hs0, hs⟩ := Hsw
      rcases hs with ⟨hlen, -, hnil⟩ | ⟨hlen, hpre⟩
      · obtain ⟨rfl, rfl⟩ := hnil rfl
        wp_auto
        wp_for_post
        iframe
        iexists rs ++ [q]
        rw [hW]
        iframe
        isplitr
        · ipureintro
          intro r hr
          simp only [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact Hrs r hr
          · exact hlen
        iapply BigSepL.bigSepL_snoc.2
        iframe #
      · simp only [List.append_nil] at hpre
        obtain ⟨rfl, rfl⟩ := prefix_squeeze hs0 hpre
        wp_auto
        wp_for_post
        iframe
        iexists rs
        iframe
        isplitr
        · ipureintro; exact Hrs
        iframe #
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end Perennial.rabia.internal.tcp
