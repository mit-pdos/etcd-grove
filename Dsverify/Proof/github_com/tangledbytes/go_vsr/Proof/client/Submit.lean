/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/client/Submit.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension.
-/
/-
`(*Client).Submit`: a received reply's payload pushed on the response queue (with its fact); any
other event logged.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.client
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.client.Slog
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.queue

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : client.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]
variable [models_lab.jsoncodec.JsonCodec GF]
variable [events.Assumptions] [log.slog.Assumptions] [queue.Assumptions]

set_option goose.wp.extras true

theorem client.Client.Submit.wp_proof
    (wp_Logger_Error : log.slog.Logger.Error.spec (GF := GF) (hG := hG))
    (wp_Push : queue.Queue.Push.spec (GF := GF) (hG := hG)) :
    client.Client.Submit.spec (GF := GF) (hG := hG) := by
  intro cl γ c st tcp ev
  wp_start as ⟨Hcl, #Hev⟩
  iunfold client.isClient at Hcl
  icases Hcl with ⟨%v, %mems, %F, %jc, Hv, %Hv, #Hmems, Hok, Hnet, Hsnd, #Hprotos, %Ht, #Hlog,
    #Hcodec, #Hkit, #Hq, Hpend⟩
  unfold network.netEvOk
  icases Hev with ⟨%m, #Hevm, #Hfm, #Haddr⟩
  unfold events.isEvent
  icases Hevm with ⟨%d, #Hep, #Hpay⟩
  iStructNamed Hep
  wp_auto
  by_cases hty : events.typeOf m = W8 2
  · cases m
    case reply id cid vn res =>
      simp only [events.payloadOf]
      icases Hpay with ⟨%x, %Hx⟩
      obtain ⟨rfl, hid, hcid, hvn, hres⟩ := Hx
      simp only [hty, _root_.decide_true]
      wp_auto
      wp_apply (wp_Push events.Reply.ty
        (fun rep : events.Reply => VsrGhost.fact γ (.msg (.reply (uint.nat rep.ID')
          (uint.nat rep.ClientID') (uint.nat rep.ViewNum') rep.Result')))) $$ []
      · iframe #
        rw [hid, hcid, hvn, hres]
        iexact Hfm
      iapply HΦ
      unfold client.isClient
      iexists v, mems, F, jc
      iframe
      iframe #
      ipureintro; exact ⟨Hv, Ht⟩
    all_goals exact absurd hty (by simp [events.typeOf])
  · simp only [hty, _root_.decide_false]
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.GoType.InterfaceType [])))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType [])
      [interface.mkOk go.string #(go!"event"), interface.mkOk events.NetworkEvent.ty #ev]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_Logger_Error _ _ _
      [interface.mkOk go.string #(go!"event"), interface.mkOk events.NetworkEvent.ty #ev] _
      $$ [Hsl] as -
    · iframe; iframe #
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iapply log.slog.argOk_string
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iapply log.slog.argOk_noFmt
        intro ii hii; cases hii
        exact ⟨by go_type_set, by go_type_set⟩
      iapply BigSepL.bigSepL_nil.2; itrivial
    iapply HΦ
    unfold client.isClient
    iexists v, mems, F, jc
    iframe
    iframe #
    ipureintro; exact ⟨Hv, Ht⟩

end proof

end Perennial.github_com.tangledbytes.go_vsr.pkg
