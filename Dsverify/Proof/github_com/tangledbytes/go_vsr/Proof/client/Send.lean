/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/client/Send.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension.
-/
/-
`(*Client).sendRequest`: the pending request's event written on a connection to `to` through the
client's network (`network.Network.Send` with a one-shot callback: `events.Event.ToWriter`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.client

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : client.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]
variable [network.Assumptions] [events.Assumptions] [net.Assumptions] [encoding.json.Assumptions]

set_option goose.wp.extras true

instance network.isNet_persistent' (n : GoInterface) (γ : VsrGhost.Names) :
    Persistent (network.isNet (GF := GF) n γ) := by
  unfold network.isNet; infer_instance

instance network.netAddrOk_persistent' (n : GoInterface) (a : ipv4port.IPv4Port) :
    Persistent (network.netAddrOk (GF := GF) n a) := by
  unfold network.netAddrOk; infer_instance

theorem client.Client.wp_sendRequest
    (wp_TCP_Send : network.TCP.Send.spec (GF := GF) (hG := hG))
    (wp_ToWriter : ∀ _jc : models_lab.jsoncodec.JsonCodec GF,
      events.Event.ToWriter.spec (GF := GF) (hG := hG))
    (cl : Loc) (v : client.Client) (γ : VsrGhost.Names)
    (F : List w8 → Bool → w64 × w64) (jc : models_lab.jsoncodec.JsonCodec GF)
    (op : GoString) (to : ipv4port.IPv4Port) (hop : PlainStr op) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.client ∗
        ⌜(VsrWire.line (.request (uint.nat v.state'.RequestNumber') (uint.nat v.state'.ID')
          op)).length < 2 ^ 60⌝ ∗
        cl ↦ v ∗ network.isNet v.net' γ ∗ network.netSender v.net' ∗
        network.netAddrOk v.net' to ∗ network.netProtos γ ∗
        encoding.json.codecSet (GF := GF) ∗
        encoding.json.kitCodecOk (jc := jc) F ∗
        VsrGhost.fact γ (.msg (.request (uint.nat v.state'.RequestNumber')
          (uint.nat v.state'.ID') op)) }}
      (App (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"sendRequest"))
        (Val #to)) (Val #op))
    {{ (err : GoInterface), RET #err; cl ↦ v ∗ network.netSender v.net' ∗
        bufio.errOrNil err }} := by
  wp_start as ⟨%hline, Hv, #Hnet, Hsnd, #Hto, #Hprotos, #Hcodec, #Hkit, #Hfact⟩
  unfold network.isNet network.netSender network.netAddrOk
  icases Hnet with ⟨%tcp, %me, %Hn, #Htcp⟩
  icases Hsnd with ⟨%tcp', %Hn', Hsnd⟩
  icases Hto with ⟨%tcp'', %Hn'', #Hto⟩
  rw [Hn] at Hn' Hn''
  simp only [interface.mkOk, GoInterface.ok.injEq] at Hn' Hn''
  have e1 : tcp' = tcp := (GoGlobalContext.intoVal_inj_loc
    (congrArg GoInterfaceOk.v Hn')).symm
  have e2 : tcp'' = tcp := (GoGlobalContext.intoVal_inj_loc
    (congrArg GoInterfaceOk.v Hn'')).symm
  subst e1 e2
  wp_auto
  simp only [Hn, interface.mkOk]
  wp_apply (wp_TCP_Send tcp'' γ me to _
    (req_ptr ↦ events.Request.mk v.state'.RequestNumber' v.state'.ID' op)
    (req_ptr ↦ events.Request.mk v.state'.RequestNumber' v.state'.ID' op)) $$ [Hsnd req]
    as %err ⟨Hsnd, #Herr, _⟩
  · iframe
    iframe #
    unfold network.sendFn
    iintro %w %Φ' Hws Hreq HΦ'
    wp_auto
    wp_alloc ev as Hev
    ipersist Hev
    letI := jc
    wp_apply (wp_ToWriter jc F γ ev
      (.request (uint.nat v.state'.RequestNumber') (uint.nat v.state'.ID') op) w) $$ [Hws]
      as %err ⟨Hws, #Herr⟩
    · iframe
      iframe #
      isplitr
      · unfold events.isEvent
        iexists (interface.mkOk events.Request.ty
          #(events.Request.mk v.state'.RequestNumber' v.state'.ID' op))
        simp only [events.typeOf, events.payloadOf]
        isplitr
        · iexact Hev
        iexists _
        ipureintro
        exact ⟨rfl, rfl, rfl, rfl⟩
      ipureintro
      exact ⟨hop, ⟨by word, by word⟩, hline⟩
    iapply HΦ' $$ Hws Herr Hreq
  iapply HΦ
  iframe
  iframe #
  ipureintro; rfl

end proof

end Perennial.github_com.tangledbytes.go_vsr.pkg
