/-
The proofs of `log.Logs.MarshalJSON` (`json.Marshal([]Log(l))`, over the main tree's
`encoding.json.Marshal.spec`) and of `log.Logs.UnmarshalJSON` (`Spec/log.lean`): `var logs []Log; json.Unmarshal(data,
&logs)`, then `*l = logs`, over the main tree's `encoding.json.Unmarshal.spec` (a section
hypothesis, linked in `examples/vsrnet/Link.lean`): a `*[]log.Log` has no `JSONModelUnmarshal`, so
the dispatch takes the registered codec's route (`codecRoute J F`). Round 9 (notes/dsv-vr.md).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.log
public import Spec.encoding.json.Codec.Unmarshal
public import Spec.encoding.json.Codec.Marshal

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : log.Assumptions] [encoding.json.Assumptions]

set_option goose.wp.extras true

theorem log.Logs.UnmarshalJSON.wp_proof
    (wp_Unmarshal : encoding.json.Unmarshal.spec (GF := GF) (hG := hG)) :
    log.Logs.UnmarshalJSON.spec (GF := GF) (hG := hG) := by
  intro J F l sl0 data dq es hval hdec
  wp_start as ⟨#Hroute, Hl, Hd⟩
  wp_auto
  ihave Hdep := hdec logs_ptr $$ logs
  ihave #Hvia := encoding.json.unmarshalVia_codec J F _ (log.logs_unmarshalsByCodec logs_ptr)
    $$ Hroute
  wp_apply wp_Unmarshal J F data _ _ _ _ $$ [Hd Hdep] as %err Hpost
  · iframe
    iexact Hvia
  icases Hpost with ⟨Hd, Hret⟩
  iunfold encoding.json.unmarshalRet at Hret
  icases Hret with (⟨%Hvalid, %ok, %Hok', ⟨%Hok1, %sl, Hp, Hown, Hcap⟩⟩ | ⟨⟨%Hnv, -⟩, -⟩)
  rotate_left
  · exact absurd hval Hnv
  subst Hok1
  have herr : err = interface.nil := Hok'.2 rfl
  subst herr
  wp_auto
  iapply HΦ
  iexists sl
  iframe

theorem log.Logs.MarshalJSON.wp_proof
    (wp_Marshal : encoding.json.Marshal.spec (GF := GF) (hG := hG)) :
    log.Logs.MarshalJSON.spec (GF := GF) (hG := hG) := by
  intro J F sl dq es henc
  wp_start as ⟨#Hroute, Hl⟩
  wp_auto
  ihave Henc := henc $$ Hl
  ihave #Hvia := encoding.json.marshalVia_codec J F _ (log.logs_marshalsByCodec sl) $$ Hroute
  wp_apply wp_Marshal J F _ _ $$ [Henc] as %s %err Hret
  · iframe
    iexact Hvia
  iunfold encoding.json.marshalRet at Hret
  icases Hret with (⟨%Herr, %bs, Hs, Hcap, %Hbs, Hl⟩ | ⟨%Herr, %Hbs, -⟩)
  rotate_left
  · cases Hbs
  subst Herr
  cases Hbs
  iapply HΦ
  iframe

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
