/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/client/CheckResult.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension.
-/
/-
`(*Client).CheckResult`: the reply of the pending request, if `onReply` stored one.
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
variable [models_lab.jsoncodec.JsonCodec GF]

set_option goose.wp.extras true

/-- Close a pure goal from the Lean context. -/
local macro "pure_ctx" : tactic =>
  `(tactic| first | assumption | (constructor <;> assumption) | (refine ⟨?_, ?_, ?_⟩ <;> assumption))

/-- Close the leading pure conjuncts of an Iris goal from the Lean context. -/
local macro "ipures" : tactic =>
  `(tactic| repeat' (first | (isplitr; · (ipureintro; pure_ctx)) | (ipureintro; pure_ctx)))

theorem client.Client.CheckResult.wp_proof :
    client.Client.CheckResult.spec (GF := GF) (hG := hG) := by
  intro cl γ c st
  wp_start as Hcl
  iunfold client.isClient at Hcl
  icases Hcl with ⟨%v, %mems, %F, %jc, Hv, %Hv, #Hmems, Hok, Hnet, Hsnd, #Hprotos, %Ht, #Hlog,
    #Hcodec, #Hkit, #Hq, Hpend⟩
  rcases st with ⟨n, pend⟩
  rcases pend with _ | op
  · -- nothing pending: no result
    icases Hpend with %Hp
    wp_auto
    simp only [Hp.2]
    wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold client.isClient
    iexists v, mems, F, jc
    iframe
    iframe #
    ipures
  · icases Hpend with ⟨%Hplain, #Hfreq, Hpend⟩
    icases Hpend with (⟨%r, %x, %Hr, #Hx, Htm⟩ | ⟨%rp, %rep, %Hr, Hrep, #Hfrep⟩)
    · -- the request still pending: no result
      wp_auto
      simp only [Hr.2.1]
      wp_auto
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold client.isClient
      iexists v, mems, F, jc
      dsimp only
      iframe
      iframe #
      ipures
      ileft
      ipures
      iexact Htm
    · -- the reply: returned, nothing pending
      obtain ⟨hreq, hres, hid, hcid⟩ := Hr
      wp_auto
      subst hres
      ihave %hrp := typedPointsto_not_null $$ Hrep
      simp only [hrp, _root_.decide_false]
      wp_auto
      iapply HΦ
      simp only [↓reduceIte]
      dsimp only at hid
      isplitr
      · ipureintro; exact ⟨rfl, hid, hcid⟩
      iframe #
      unfold client.isClient
      iexists _, mems, F, jc
      dsimp only
      iframe
      iframe #
      ipures
      done

end proof

end Perennial.github_com.tangledbytes.go_vsr.pkg
