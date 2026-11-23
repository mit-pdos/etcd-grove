/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/client/Request.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension.
-/
/-
`(*Client).Request`: the request `n + 1` pending (its timer started, its first send attempted).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.client.Send
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
variable [time.Assumptions]

set_option goose.wp.extras true

theorem client.Client.Request.wp_proof
    (wp_TCP_Send : network.TCP.Send.spec (GF := GF) (hG := hG))
    (wp_ToWriter : ∀ _jc : models_lab.jsoncodec.JsonCodec GF,
      events.Event.ToWriter.spec (GF := GF) (hG := hG)) :
    client.Client.Request.spec (GF := GF) (hG := hG) := by
  intro cl γ c n op
  wp_start as ⟨%Hn, %Hop, %Hmb, %Hline, Hcl, #Hfact⟩
  iunfold client.isClient at Hcl
  icases Hcl with ⟨%v, %mems, %F, %jc, Hv, %Hv, #Hmems, #Hok, #Hnet, Hsnd, #Hprotos, %Ht, #Hlog,
    #Hcodec, #Hkit, #Hq, Hpend⟩
  icases Hpend with %Hp
  wp_auto
  simp only [Hp.1]
  wp_auto
  irename «$r0» => Hr
  ipersist Hr
  wp_apply (time.NewTimer.wp v.time' _ Ht) as %tm Htm
  dsimp only
  ihave %Hml := ownSlice_len $$ Hmems
  wp_method_call
  wp_call
  wp_auto
  have hlen0 : ¬ uint.Z v.state'.LastKnownClusterMembers'.len = 0 := by
    have := Hv.2.2; word
  simp only [hlen0, ↓reduceIte]
  wp_auto
  have hb : 0 ≤ sint.Z (v.state'.LastKnownViewNumber' % v.state'.LastKnownClusterMembers'.len) ∧
      sint.Z (v.state'.LastKnownViewNumber' % v.state'.LastKnownClusterMembers'.len) <
        sint.Z v.state'.LastKnownClusterMembers'.len := by
    have := Hv.2.2
    have hy : 0 < (v.state'.LastKnownClusterMembers'.len).toNat := by
      have := hlen0; word
    have h1 : (v.state'.LastKnownViewNumber' % v.state'.LastKnownClusterMembers'.len).toNat <
        (v.state'.LastKnownClusterMembers'.len).toNat := by
      rw [BitVec.toNat_umod]; exact Nat.mod_lt _ hy
    have h2 := Hml.2
    constructor <;> word
  simp only [hb, _root_.and_self, ↓reduceIte]
  list_elem mems (sint.nat (v.state'.LastKnownViewNumber' % v.state'.LastKnownClusterMembers'.len))
    as a
  wp_apply wp_load_slice_index _ _ mems DFrac.discard a hb.1 $$ [Hmems] as -
  · isplitl
    · iexact Hmems
    ipureintro
    exact Ha_lookup
  ihave Hoka := BigSepL.bigSepL_lookup Ha_lookup $$ Hok
  have hrn : uint.nat (v.state'.RequestNumber' + W64 1) = n + 1 := by
    have := Hv.2.1; dsimp only at this; word
  have hline : (VsrWire.line (.request (n + 1) c op)).length < 2 ^ 60 := by
    exact Hline
  wp_apply (client.Client.wp_sendRequest wp_TCP_Send wp_ToWriter cl _ γ F jc op a Hop) $$ [Hv Hsnd] as %err ⟨Hv, Hsnd, #Herr⟩
  · iframe
    iframe #
    dsimp only
    rw [hrn, Hv.1]
    isplitr
    · ipureintro; exact hline
    iexact Hfact
  cases err
  all_goals
    wp_auto
    iapply HΦ
    unfold client.isClient
    iexists _, mems, F, jc
    isplitl [Hv]
    · iexact Hv
    dsimp only
    iframe
    iframe #
    isplitr
    · ipureintro; exact ⟨Hv.1, hrn, Hv.2.2⟩
    isplitr
    · ipureintro; exact Ht
    isplitr
    · ipureintro; exact ⟨Hop, hline⟩
    ileft
    isplitr
    · ipureintro
      refine ⟨rfl, Hp.2, ?_, ?_, rfl⟩
      · exact hrn
      · exact Hv.1
    iexists _
    iexact Htm

end proof

end Perennial.github_com.tangledbytes.go_vsr.pkg
