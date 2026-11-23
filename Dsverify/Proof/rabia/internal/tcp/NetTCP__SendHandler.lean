/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/NetTCP__SendHandler.lean`,
run `rabia-r1wake-1`: the writer is `wrOwn` (the revised bufio's over `Net/`'s connection); the
encodings' bounds are network's `bmsgOk_encBound`/`replyOk_encBound`.)

The proof of `rabia/internal/tcp.(*NetTCP).SendHandler(j)`: server `k`'s send routine to server
`j` writes, after its handshake, its channel's values in order: the serializer's `B_k` in order and
the router's replies to `j` (`netP`).
-/
module

public import Dsverify.Proof.rabia.internal.tcp.NetLemmas
public import Dsverify.Proof.rabia.roles.server.layers.network.Basics

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
  rabia.internal.message rabia.internal.config

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.internal.tcp.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]
variable [msg_sem : rabia.internal.message.Assumptions]

set_option goose.wp.extras true

instance ite_persistent' {P : Prop} [Decidable P] (A B : IProp GF) [Persistent A] [Persistent B] :
    Persistent (if P then A else B) := by split <;> assumption

/-- Network's `bmsgOk_encBound`: a broadcast message's encoding fits a frame. -/
theorem bmsgOk_encBound_pending (γ : Names) (cf : RCfg) (X : Nat) (m : MsgV) :
    bmsgOk (GF := GF) γ cf X m ⊢ bmsgOk γ cf X m ∗ ⌜(encMsg m).length < 2 ^ 32⌝ := by
  exact Perennial.rabia.roles.server.layers.network.bmsgOk_encBound γ cf X m

/-- Network's `replyOk_encBound`. -/
theorem replyOk_encBound_pending (γ : Names) (cf : RCfg) (j : Nat) (m : MsgV) :
    replyOk (GF := GF) γ cf j m ⊢ replyOk γ cf j m ∗ ⌜(encMsg m).length < 2 ^ 32⌝ := by
  exact Perennial.rabia.roles.server.layers.network.replyOk_encBound γ cf j m

/-- The bytes a send routine to `j` has written: its handshake and the messages `fs`. -/
def sendSt (γ : Names) (cf : RCfg) (k j : Nat) (γo : OrdNames) (bw : Loc) (cid : Nat)
    (f : List Nat) (fs : List MsgV) : IProp GF :=
  iprop(ordCons γo f ∗ ⌜f.length = 2 ∧ f.getD 0 0 = (bcastPart fs).length ∧
      ∀ m ∈ fs, (encMsg m).length < 2 ^ 32⌝ ∗
    wrOwn bw cid false (netP γ j) (hsBytes k ++ frames (fs.map encMsg)) [] interface.nil ∗
    bcastLb γ k (bcastPart fs) ∗ [∗list] m ∈ fs.filter (·.ty = tyProposalReply), replyOk γ cf j m)

theorem wp_NetTCP_SendHandler (γ : Names) (cf : RCfg) (k : Nat) (hk : k < cf.n) (t : Loc)
    (to : w64) (j : Nat) (hj : sint.Z to = j) (hjn : j < cf.n) (done : GoChan) (wg : Loc) (scs wrs : GoSlice)
    (chs : List GoChan) (ws : List Loc) (ch : GoChan) (bw : Loc) (cid : Nat) (γo : OrdNames)
    (hch : chs[j]? = some ch) (hbw : ws[j]? = some bw) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ shared γ ∗ cfgIs γ.rab cf ∗
      t.[NetTCP, go!"Done"] ↦□ done ∗ doneChan done ∗ t.[NetTCP, go!"Wg"] ↦□ wg ∗ wgTok wg ∗
      t.[NetTCP, go!"SendChan"] ↦□ scs ∗ scs ↦*□ chs ∗ isOrdChan γo ch 2 (sendP γ cf k j) ∗
      t.[NetTCP, go!"Writers"] ↦□ wrs ∗ wrs ↦*□ ws ∗
      sendSt γ cf k j γo bw cid [0, 0] [] }}
    (App (Val (t @!! go.GoType.PointerType NetTCP.ty @!! go!"SendHandler")) (Val #to))
  {{ RET #(); True }} := by
  wp_start as ⟨#Hsh, #Hcf, #HD, #Hdone, #HWg, Htok, #HSC, #Hscs, #Hord, #HW, #Hwrs, Hst⟩
  ihave %Hok := cfgIs_ok γ.rab cf $$ Hcf
  have hkm : k < maxS := Nat.lt_of_lt_of_le hk (RCfg.n_le_maxS cf Hok)
  wp_apply wp_with_defer as %defer Hdefer
  unfold doneChan
  icases Hdone with ⟨%γd, #Hdbag⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hscs
  ihave %Hwl := ownSlice_len _ _ _ $$ Hwrs
  have hjl : j < chs.length := (List.getElem?_eq_some_iff.1 hch).1
  have hjw : j < ws.length := (List.getElem?_eq_some_iff.1 hbw).1
  ihave HI : (∃ (f : List Nat) (fs : List MsgV), "Hst" ∷ sendSt γ cf k j γo bw cid f fs : IProp GF)
    $$ [Hst]
  · iexists _, _; iexact Hst
  wp_for_core
  iNamed HI
  wp_auto_lc 1
  irename Hlc1 => Hlc2
  cleanup_bool_decide
  wp_auto_lc 1
  have hbs : 0 ≤ sint.Z to ∧ sint.Z to < sint.Z scs.len := by
    have h1 := Hsl.1; rw [hj]; constructor
    · omega
    · word
  have hbw' : 0 ≤ sint.Z to ∧ sint.Z to < sint.Z wrs.len := by
    have h1 := Hwl.1; rw [hj]; constructor
    · omega
    · word
  have htj : (sint.Z to).toNat = j := by rw [hj]; simp
  simp only [hbs, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index scs _ chs _ ch hbs.1 $$ [Hscs] with -
  · iframe #; ipureintro; rw [htj]; exact hch
  unfold sendSt
  iNamed Hst
  icases Hst with ⟨Hcons, %Hf, Hw, #Hlb, #Hreps⟩
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
    iexists GoSlice, inferInstance, inferInstance, inferInstance, inferInstance, ch, γo.chanName
    isplitr
    · ipureintro; rfl
    ihave #Hch : isChan ch γo.chanName GoSlice $$ [Hord]
    · unfold isOrdChan; icases Hord with ⟨$, -⟩
    iframe Hch
    iapply ord_rcv_au $$ Hord [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok %Hok ⟨%i, %Hi, Hv, Hcons⟩
    subst Hok
    wp_auto
    simp only [hbw', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index wrs _ ws _ bw hbw'.1 $$ [Hwrs] with -
    · iframe #; ipureintro; rw [htj]; exact hbw
    ihave ⟨%m, #Hvm, #Hv⟩ := sendP_open γ cf k j i (f.getD i 0) v $$ Hv
    -- the message `m` and its facts: `B_k`'s next, or a reply to `j`
    ihave Hnew : |={⊤}=> (bcastLb γ k (bcastPart (fs ++ [m])) ∗
        ([∗list] m' ∈ (fs ++ [m]).filter (·.ty = tyProposalReply), replyOk γ cf j m') ∗
        ⌜(f.set i (f.getD i 0 + 1)).getD 0 0 = (bcastPart (fs ++ [m])).length ∧
          (encMsg m).length < 2 ^ 32⌝) $$ []
    · have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · simp only [↓reduceIte]
        icases Hv with ⟨%l, #Hl, %Hlm⟩
        rw [Hf.2.1] at Hlm
        ihave %Hcmp := bcastLb_agree γ k (bcastPart fs) l $$ [$Hlb $Hl]
        have hpre : bcastPart fs ++ [m] <+: l := by
          rcases Hcmp with h | h
          · obtain ⟨t, rfl⟩ := h
            simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at Hlm
            cases t with
            | nil => simp at Hlm
            | cons x t => simp at Hlm; subst Hlm; exact ⟨t, by simp⟩
          · have := h.length_le
            have := (List.getElem?_eq_some_iff.1 Hlm).1
            omega
        imod bcast_elem γ cf k hkm l _ m Hlm $$ [$Hsh $Hcf $Hl] with #Hm
        ihave %Hty := bmsgOk_notReply γ cf k m $$ Hm
        icases bmsgOk_encBound_pending γ cf k m $$ Hm with ⟨-, %Hmb⟩
        have hbp : bcastPart (fs ++ [m]) = bcastPart fs ++ [m] := by
          simp [bcastPart, Hty]
        have hfl : (fs ++ [m]).filter (·.ty = tyProposalReply) = fs.filter (·.ty = tyProposalReply) := by
          simp [Hty]
        rw [hbp, hfl]
        imodintro
        isplitl
        · iapply bcastLb_prefix γ k l _ hpre $$ Hl
        iframe #
        ipureintro
        obtain ⟨hf1, hf2, -⟩ := Hf
        refine ⟨?_, Hmb⟩
        match f, hf1 with
        | [a, b], _ => simp at hf2 ⊢; omega
      · simp only [Nat.one_ne_zero, ↓reduceIte]
        ihave %Hty := replyOk_ty γ cf j m $$ Hv
        icases replyOk_encBound_pending γ cf j m $$ Hv with ⟨-, %Hmb⟩
        have hbp : bcastPart (fs ++ [m]) = bcastPart fs := by
          simp [bcastPart, Hty]
        have hfl : (fs ++ [m]).filter (·.ty = tyProposalReply) =
            fs.filter (·.ty = tyProposalReply) ++ [m] := by
          simp [Hty]
        rw [hbp, hfl]
        imodintro
        isplitr
        · iexact Hlb
        isplitr
        · iapply BigSepL.bigSepL_snoc.2
          isplitr
          · iexact Hreps
          · iexact Hv
        ipureintro
        obtain ⟨hf1, hf2, -⟩ := Hf
        refine ⟨?_, Hmb⟩
        match f, hf1 with
        | [a, b], _ => simp at hf2 ⊢; omega
    imod Hnew with ⟨#Hlb', #Hreps', %Hf'⟩
    obtain ⟨Hf', Hmb⟩ := Hf'
    have hW : hsBytes k ++ frames (fs.map encMsg) ++ [] ++ model.frame (encMsg m) =
        hsBytes k ++ frames ((fs ++ [m]).map encMsg) := by
      simp [frames_append, frames_cons, frames_nil]
    ihave #HP : netP γ j cid (hsBytes k ++ frames ((fs ++ [m]).map encMsg)) $$ []
    · unfold netP
      iright
      iexists cf, k, fs ++ [m]
      isplitr
      · iexact Hcf
      isplitr
      · ipureintro
        refine ⟨hk, List.prefix_refl _, ?_⟩
        intro r hr
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact Hf.2.2 r hr
        · exact Hmb
      iframe #
    wp_apply wp_writeFlush bw cid false (netP γ j) _ [] _ v _ (encMsg m) $$ [$Hw $Hvm]
      as %e ⟨%sent', %pend', %Hs, -, Hw⟩
    · iframe %Hmb
      rw [hW]; iexact HP
    rcases e with ei | _
    · wp_auto
      wp_for_post
      wp_apply wp_wgDone wg $$ [$Htok]
      iapply HΦ
      itrivial
    · obtain ⟨rfl, rfl⟩ := Hs.2.2 rfl
      wp_auto
      wp_for_post
      iframe
      iexists f.set i (f.getD i 0 + 1), fs ++ [m]
      rw [hW]
      unfold named
      iframe Hcons Hw
      iframe #
      ipureintro
      refine ⟨by simp [Hf.1], Hf', ?_⟩
      intro r hr
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact Hf.2.2 r hr
      · exact Hmb
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end Perennial.rabia.internal.tcp
