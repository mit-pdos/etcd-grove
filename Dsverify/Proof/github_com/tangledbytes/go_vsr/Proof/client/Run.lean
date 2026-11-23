/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/client/Run.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension.
-/
/-
`(*Client).Run`: at the pending request's timeout, its broadcast to every member; then one
reply from the response queue processed (`onReply`: the pending request's reply is stored).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.client.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.client.Slog
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.queue.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.time.Results

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
variable [network.Assumptions] [events.Assumptions] [net.Assumptions] [encoding.json.Assumptions]
variable [time.Assumptions] [queue.Assumptions] [log.slog.Assumptions]
variable (wp_TCP_Send : network.TCP.Send.spec (GF := GF) (hG := hG))
variable (wp_ToWriter : ∀ _jc : models_lab.jsoncodec.JsonCodec GF,
  events.Event.ToWriter.spec (GF := GF) (hG := hG))
variable (wp_Logger_Error : log.slog.Logger.Error.spec (GF := GF) (hG := hG))
variable (wp_Logger_Debug : log.slog.Logger.Debug.spec (GF := GF) (hG := hG))

set_option goose.wp.extras true

/-- Close a pure goal from the Lean context. -/
local macro "pure_ctx" : tactic =>
  `(tactic| first | assumption | (constructor <;> assumption) | (refine ⟨?_, ?_, ?_⟩ <;> assumption))

/-- Close the leading pure conjuncts of an Iris goal from the Lean context. -/
local macro "ipures" : tactic =>
  `(tactic| repeat' (first | (isplitr; · (ipureintro; pure_ctx)) | (ipureintro; pure_ctx)))

include wp_Logger_Error in
theorem client.Logger.wp_Error_err (l : Loc) (msg s : GoString)
    (sl : GoSlice) (e : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog ∗ log.slog.isLogger l ∗
        bufio.errOrNil e ∗ sl ↦* [interface.mkOk go.string #s, e] }}
      (App (App (Val (l @!! go.GoType.PointerType log.slog.Logger.ty @!! go!"Error")) (Val #msg))
        (Val #sl))
    {{ RET #(); True }} := by
  wp_start_folded as ⟨#Hl, #He, Hsl⟩
  ihave #Ha := log.slog.argOk_of_errOrNil e $$ He
  wp_apply wp_Logger_Error l msg sl _ (DFrac.own 1) $$ [$Hsl] as -
  · iframe #
    isplitr
    · iapply log.slog.argOk_string
    iapply BigSepL.bigSepL_nil.2
    itrivial
  iapply HΦ; itrivial

/-- The arguments `onReply` logs. -/
theorem client.replyArgs_ok (rep : events.Reply) :
    ⊢ [∗list] x ∈ [interface.mkOk go.string #(go!"reply"), interface.mkOk events.Reply.ty #rep],
      log.slog.argOk (GF := GF) x := by
  iapply BigSepL.bigSepL_cons.2
  isplitr
  · iapply log.slog.argOk_string
  iapply BigSepL.bigSepL_cons.2
  isplitr
  · iapply log.slog.argOk_noFmt
    intro ii hii; cases hii
    exact ⟨by go_type_set, by go_type_set⟩
  iapply BigSepL.bigSepL_nil.2; itrivial

include wp_TCP_Send wp_ToWriter in
theorem client.Client.wp_broadcastRequest (cl : Loc) (v : client.Client) (γ : VsrGhost.Names)
    (F : List w8 → Bool → w64 × w64) (jc : models_lab.jsoncodec.JsonCodec GF)
    (op : GoString) (mems : List ipv4port.IPv4Port) (hop : PlainStr op) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.client ∗
        ⌜(VsrWire.line (.request (uint.nat v.state'.RequestNumber') (uint.nat v.state'.ID')
          op)).length < 2 ^ 60⌝ ∗
        cl ↦ v ∗ v.state'.LastKnownClusterMembers' ↦*□ mems ∗
        ([∗list] a ∈ mems, network.netAddrOk v.net' a) ∗
        network.isNet v.net' γ ∗ network.netSender v.net' ∗ network.netProtos γ ∗
        encoding.json.codecSet (GF := GF) ∗
        encoding.json.kitCodecOk (jc := jc) F ∗
        VsrGhost.fact γ (.msg (.request (uint.nat v.state'.RequestNumber')
          (uint.nat v.state'.ID') op)) }}
      (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"broadcastRequest"))
        (Val #op))
    {{ (err : GoInterface), RET #err; cl ↦ v ∗ network.netSender v.net' ∗
        bufio.errOrNil err }} := by
  wp_start as ⟨%hline, Hv, #Hmems, #Hok, #Hnet, Hsnd, #Hprotos, #Hcodec, #Hkit, #Hfact⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hmems
  ihave IH : iprop(∃ (k : w64) (mm : ipv4port.IPv4Port),
      "i" ∷ i_ptr ↦ k ∗ "member" ∷ member_ptr ↦ mm ∗ "Hv" ∷ cl ↦ v ∗
      "Hsnd" ∷ network.netSender v.net' ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (mems.length : Int)⌝) $$ [i member Hv Hsnd]
  · iexists _, _
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z k).toNat < mems.length := by word
    obtain ⟨a, Ha⟩ : ∃ a, mems[(sint.Z k).toNat]? = some a :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z v.state'.LastKnownClusterMembers'.len
      from ⟨Hk.1, Hif⟩]
    wp_apply wp_load_slice_index _ (sint.Z k) mems DFrac.discard a Hk.1 $$ [Hmems] as -
    · isplitl
      · iexact Hmems
      ipureintro; exact Ha
    ihave Hoka := BigSepL.bigSepL_lookup Ha $$ Hok
    wp_apply (client.Client.wp_sendRequest wp_TCP_Send wp_ToWriter cl v γ F jc op a hop) $$ [Hv Hsnd] as %err ⟨Hv, Hsnd, #Herr⟩
    · iframe; iframe #; ipureintro; exact hline
    cases err
    case nil =>
      wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    case ok =>
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      iframe #
  · iapply HΦ
    iframe
    unfold bufio.errOrNil
    ileft; ipureintro; rfl

/-- A reply's fact, as the response queue carries it. -/
abbrev client.replyFact (γ : VsrGhost.Names) (rep : events.Reply) : IProp GF :=
  VsrGhost.fact γ (.msg (.reply (uint.nat rep.ID') (uint.nat rep.ClientID')
    (uint.nat rep.ViewNum') rep.Result'))

include wp_Logger_Debug in
theorem client.Client.wp_onReply (cl : Loc) (γ : VsrGhost.Names) (c : Nat) (st : client.St)
    (rep : events.Reply) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.client ∗
        client.isClient cl γ c st ∗ client.replyFact γ rep }}
      (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"onReply")) (Val #rep))
    {{ RET #(); client.isClient cl γ c st }} := by
  wp_start as ⟨Hcl, #Hrep⟩
  iunfold client.isClient at Hcl
  icases Hcl with ⟨%v, %mems, %F, %jc, Hv, %Hv, #Hmems, Hok, Hnet, Hsnd, #Hprotos, %Ht, #Hlog,
    #Hcodec, #Hkit, #Hq, Hpend⟩
  ihave #Hargs := client.replyArgs_ok (GF := GF) rep
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.GoType.InterfaceType [])))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType [])
    [interface.mkOk go.string #(go!"reply"), interface.mkOk events.Reply.ty #rep]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_auto
  wp_apply wp_Logger_Debug _ _ _ _ _ $$ [Hsl1] as -
  · iframe; iframe #
  -- no request pending (nothing, or its reply already stored): only a log
  rcases st with ⟨n, pend⟩
  rcases pend with _ | op
  · icases Hpend with %Hp
    simp only [Hp.1, _root_.decide_true]
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.GoType.InterfaceType [])))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType [])
      [interface.mkOk go.string #(go!"reply"), interface.mkOk events.Reply.ty #rep]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_auto
    wp_apply wp_Logger_Debug _ _ _ _ _ $$ [Hsl2] as -
    · iframe; iframe #
    iapply HΦ
    unfold client.isClient
    iexists v, mems, F, jc
    iframe
    iframe #
    ipures
  · icases Hpend with ⟨%Hpl, #Hfreq, Hor⟩
    icases Hor with (⟨%r, %x, %Hr, #Hx, Htm⟩ | ⟨%rp, %rep', %Hr, Hrp, #Hfrep⟩)
    · ihave %hrn := typedPointsto_not_null $$ Hx
      obtain ⟨hreq, hres, hxid, hxcid, hxop⟩ := Hr
      simp only [hreq, hrn, _root_.decide_false]
      iStructNamed Hx
      wp_auto
      simp only [hreq]
      wp_auto
      by_cases h1 : x.ID' = rep.ID'
      · simp only [h1, _root_.decide_true]
        wp_auto
        simp only [hreq]
        wp_auto
        by_cases h2 : x.ClientID' = rep.ClientID'
        · simp only [h2, _root_.decide_true]
          wp_auto
          wp_bind (App (Val (GoInstruction (CompositeLiteral
            (go.SliceType (go.GoType.InterfaceType []))))) (Val (LiteralValueV _)))
          iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType [])
            [interface.mkOk go.string #(go!"reply"), interface.mkOk events.Reply.ty #rep]
          wp_auto
          isplitl []
          · ipureintro; rfl
          iintro %sl3 ⟨Hsl3, -⟩
          wp_auto
          wp_apply wp_Logger_Debug _ _ _ _ _ $$ [Hsl3] as -
          · iframe; iframe #
          iapply HΦ
          unfold client.isClient
          iexists _, mems, F, jc
          isplitl [Hv]
          · iexact Hv
          dsimp only
          iframe
          iframe #
          ipures
          iright
          iexists ev_ptr, rep
          isplitr
          · ipureintro
            refine ⟨rfl, rfl, ?_, ?_⟩
            · rw [← h1]; exact hxid
            · rw [← h2]; exact hxcid
          iframe
          have e1 : uint.nat rep.ID' = n := by rw [← h1]; exact hxid
          have e2 : uint.nat rep.ClientID' = c := by rw [← h2]; exact hxcid
          simp only [client.replyFact, e1, e2]
          iexact Hrep
        · simp only [h2, _root_.decide_false]
          wp_auto
          iapply HΦ
          unfold client.isClient
          iexists v, mems, F, jc
          dsimp only
          iframe
          iframe #
          ipures
          ileft
          isplitr
          · ipureintro; exact ⟨hreq, hres, hxid, hxcid, hxop⟩
          iexact Htm
      · simp only [h1, _root_.decide_false]
        wp_auto
        iapply HΦ
        unfold client.isClient
        iexists v, mems, F, jc
        dsimp only
        iframe
        iframe #
        ipures
        ileft
        isplitr
        · ipureintro; exact ⟨hreq, hres, hxid, hxcid, hxop⟩
        iexact Htm
    · -- its reply already stored
      simp only [Hr.1, _root_.decide_true]
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.GoType.InterfaceType [])))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType [])
        [interface.mkOk go.string #(go!"reply"), interface.mkOk events.Reply.ty #rep]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_auto
      wp_apply wp_Logger_Debug _ _ _ _ _ $$ [Hsl2] as -
      · iframe; iframe #
      iapply HΦ
      unfold client.isClient
      iexists v, mems, F, jc
      iframe
      iframe #
      ipures
      isplitr
      · iexact Hfreq
      iright
      iexists rp, rep'
      iframe
      iframe #
      ipures


include wp_TCP_Send wp_ToWriter wp_Logger_Error wp_Logger_Debug in
theorem client.Client.Run.wp_proof : client.Client.Run.spec (GF := GF) (hG := hG) := by
  intro cl γ c st
  wp_start as Hcl
  wp_auto
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun r => iprop(⌜r = executeVal⌝ ∗ c_ptr ↦ cl ∗
    client.isClient cl γ c st))) $$ [Hcl c]
  · iunfold client.isClient at Hcl
    icases Hcl with ⟨%v, %mems, %F, %jc, Hv, %Hv, #Hmems, #Hok, #Hnet, Hsnd, #Hprotos, %Ht,
      #Hlog, #Hcodec, #Hkit, #Hq, Hpend⟩
    rcases st with ⟨n, pend⟩
    rcases pend with _ | op
    · icases Hpend with %Hp
      wp_auto
      simp only [Hp.1, _root_.decide_true]
      try wp_auto
      isplitr
      · ipureintro; rfl
      iframe c
      unfold client.isClient
      iexists v, mems, F, jc
      iframe
      iframe #
      ipures
    · icases Hpend with ⟨%Hpl, #Hfreq, Hor⟩
      icases Hor with (⟨%r, %x, %Hr, #Hx, ⟨%tst, Htm⟩⟩ | ⟨%rp, %rep', %Hr, Hrp, #Hfrep⟩)
      · ihave %hrn := typedPointsto_not_null $$ Hx
        obtain ⟨hreq, hres, hxid, hxcid, hxop⟩ := Hr
        wp_auto
        simp only [hreq, hrn, _root_.decide_false]
        wp_auto
        wp_apply (time.Timer.Done.wp v.internal'.requestTimer' tst) $$ [Htm] as %b Htm
        · iexact Htm
        cases b
        · wp_auto
          isplitr
          · ipureintro; rfl
          iframe c
          unfold client.isClient
          iexists v, mems, F, jc
          dsimp only
          iframe
          iframe #
          ipures
          ileft
          isplitr
          · ipureintro; exact ⟨hreq, hres, hxid, hxcid, hxop⟩
          iexists _
          iexact Htm
        · wp_auto
          ihave Hnil := ownSlice_nil (V := GoInterface) (DFrac.own 1)
          wp_apply wp_Logger_Debug _ _ _ [] _ $$ [Hnil] as -
          · iframe; iframe #
            iapply BigSepL.bigSepL_nil.2; itrivial
          simp only [hreq]
          iStructNamed Hx
          wp_auto
          have hline : (VsrWire.line (.request (uint.nat v.state'.RequestNumber')
              (uint.nat v.state'.ID') op)).length < 2 ^ 60 := by
            rw [Hv.1, Hv.2.1]; exact Hpl.2
          wp_apply (client.Client.wp_broadcastRequest wp_TCP_Send wp_ToWriter cl v γ F jc x.Op' mems (hxop ▸ Hpl.1))
            $$ [Hv Hsnd] as %err ⟨Hv, Hsnd, #Herr⟩
          · iframe; iframe #
            rw [hxop]
            isplitr
            · ipureintro; exact hline
            rw [Hv.1, Hv.2.1]
            iexact Hfreq
          cases err
          case ok ei =>
            wp_auto
            wp_bind (App (Val (GoInstruction (CompositeLiteral
              (go.SliceType (go.GoType.InterfaceType []))))) (Val (LiteralValueV _)))
            iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType [])
              [interface.mkOk go.string #(go!"error"), GoInterface.ok ei]
            wp_auto
            isplitl []
            · ipureintro; rfl
            iintro %sle ⟨Hsle, -⟩
            wp_auto
            wp_apply (client.Logger.wp_Error_err wp_Logger_Error _ _ go!"error" _ (GoInterface.ok ei)) $$ [Hsle]
            · iframe; iframe #
            wp_apply (time.Timer.Reset.wp v.internal'.requestTimer' tst) $$ [Htm] as Htm
            · iexact Htm
            isplitr
            · ipureintro; rfl
            iframe c
            unfold client.isClient
            iexists v, mems, F, jc
            dsimp only
            iframe
            iframe #
            ipures
            ileft
            isplitr
            · ipureintro; exact ⟨hreq, hres, hxid, hxcid, hxop⟩
            iexists _
            iexact Htm
          case nil =>
            wp_auto
            wp_apply (time.Timer.Reset.wp v.internal'.requestTimer' tst) $$ [Htm] as Htm
            · iexact Htm
            isplitr
            · ipureintro; rfl
            iframe c
            unfold client.isClient
            iexists v, mems, F, jc
            dsimp only
            iframe
            iframe #
            ipures
            ileft
            isplitr
            · ipureintro; exact ⟨hreq, hres, hxid, hxcid, hxop⟩
            iexists _
            iexact Htm
      · wp_auto
        simp only [Hr.1, _root_.decide_true]
        try wp_auto
        isplitr
        · ipureintro; rfl
        iframe c
        unfold client.isClient
        iexists v, mems, F, jc
        dsimp only
        iframe
        iframe #
        ipures
        iright
        ipures
        iframe
        iframe #
        ipureintro; exact Hr
  iintro %r ⟨%Hr, c, Hcl⟩
  subst Hr
  wp_auto
  iunfold client.isClient at Hcl
  icases Hcl with ⟨%v, %mems, %F, %jc, Hv, %Hv, #Hmems, #Hok, #Hnet, Hsnd, #Hprotos, %Ht,
    #Hlog, #Hcodec, #Hkit, #Hq, Hpend⟩
  wp_auto
  wp_apply (queue.Queue.Pop.wp events.Reply.ty
    (fun rep : events.Reply => VsrGhost.fact γ (.msg (.reply (uint.nat rep.ID')
      (uint.nat rep.ClientID') (uint.nat rep.ViewNum') rep.Result'))) v.internal'.response')
    as %rep %ok Hrep
  · iexact Hq
  ihave Hcl : client.isClient cl γ c st $$ [Hv Hsnd Hpend]
  · unfold client.isClient
    iexists v, mems, F, jc
    iframe
    iframe #
    ipures
  cases ok
  · wp_auto
    iapply HΦ $$ Hcl
  · simp only [↓reduceIte]
    wp_auto
    wp_apply (client.Client.wp_onReply wp_Logger_Debug cl γ c st rep) $$ [Hcl Hrep] as Hcl
    · iframe
    iapply HΦ $$ Hcl

end proof

end Perennial.github_com.tangledbytes.go_vsr.pkg
