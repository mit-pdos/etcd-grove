/-
The proof of `marshalAny` (`Spec/encoding/json/Codec/marshalAny.lean`): the two comma-ok assertions
decide the route as `marshalVia` does (`typeSetContains` of the value's dynamic type); a method
route calls the method value `marshalAt` is about; the codec route loads the registered codec's
`Marshal` (`getCodec`, `codecFnsWith`) and calls it under `marshalOk`.
-/
module

public import Spec.encoding.json.Codec.marshalAny
public import Spec.encoding.json.Codec.getCodec

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

theorem marshalAny.wp_proof (wp_getCodec : getCodec.spec (GF := GF) (hG := hG)) :
    marshalAny.spec (GF := GF) (hG := hG) := by
  intro J F v Ψ
  rcases v with ⟨ty, x⟩ | _
  · cases h1 : go.typeSetContains ty encoding.json.modelMarshalerPtr.ty
    · cases h2 : go.typeSetContains ty encoding.json.modelMarshaler.ty
      · simp only [marshalVia, h1, h2, Bool.false_eq_true, ↓reduceIte]
        wp_start as ⟨Hroute, Henc⟩
        wp_auto
        try simp only [h1, Bool.false_eq_true, ↓reduceIte]
        wp_auto
        try simp only [h2, Bool.false_eq_true, ↓reduceIte]
        wp_auto
        unfold codecRoute
        icases Hroute with ⟨%fm, %fu, #Hset, #Hok⟩
        wp_apply wp_getCodec fm fu $$ Hset as %c #Hc
        unfold codecFnsWith
        icases Hc with ⟨#HM, #HU, #HS⟩
        wp_auto
        unfold codecOkWith models_lab.jsoncodec.marshalOk
        icases Hok with ⟨#HmOk, -, -⟩
        wp_bind (App (Val #fm) _)
        iapply HmOk $$ Henc
        inext
        isplit
        · iintro %s %bs Hs Hcap HΨ
          wp_auto
          iapply HΦ
          unfold marshalRet
          ileft
          isplitr
          · ipureintro; rfl
          iexists bs
          iframe
        · iintro %s %err %Herr HΨ
          wp_auto
          iapply HΦ
          unfold marshalRet
          iright
          iframe
          ipureintro; exact Herr
      · simp only [marshalVia, h1, h2, Bool.false_eq_true, ↓reduceIte]
        wp_start as ⟨Hm, Henc⟩
        wp_auto
        try simp only [h1, Bool.false_eq_true, ↓reduceIte]
        wp_auto
        try simp only [h2, ↓reduceIte]
        wp_auto
        unfold marshalAt
        wp_bind (App (Val #(methods _ _ _)) _)
        iapply Hm $$ Henc
        inext
        isplit
        · iintro %s %bs Hs Hcap HΨ
          wp_auto
          iapply HΦ
          unfold marshalRet
          ileft
          isplitr
          · ipureintro; rfl
          iexists bs
          iframe
        · iintro %s %err %Herr HΨ
          wp_auto
          iapply HΦ
          unfold marshalRet
          iright
          iframe
          ipureintro; exact Herr
    · simp only [marshalVia, h1, ↓reduceIte]
      wp_start as ⟨Hm, Henc⟩
      wp_auto
      simp only [h1, ↓reduceIte]
      wp_auto
      unfold marshalAt
      wp_bind (App (Val #(methods _ _ _)) _)
      iapply Hm $$ Henc
      inext
      isplit
      · iintro %s %bs Hs Hcap HΨ
        wp_auto
        iapply HΦ
        unfold marshalRet
        ileft
        isplitr
        · ipureintro; rfl
        iexists bs
        iframe
      · iintro %s %err %Herr HΨ
        wp_auto
        iapply HΦ
        unfold marshalRet
        iright
        iframe
        ipureintro; exact Herr
  · simp only [marshalVia]
    wp_start as ⟨Hroute, Henc⟩
    wp_auto
    unfold codecRoute
    icases Hroute with ⟨%fm, %fu, #Hset, #Hok⟩
    wp_apply wp_getCodec fm fu $$ Hset as %c #Hc
    unfold codecFnsWith
    icases Hc with ⟨#HM, #HU, #HS⟩
    wp_auto
    unfold codecOkWith models_lab.jsoncodec.marshalOk
    icases Hok with ⟨#HmOk, -, -⟩
    wp_bind (App (Val #fm) _)
    iapply HmOk $$ Henc
    inext
    isplit
    · iintro %s %bs Hs Hcap HΨ
      wp_auto
      iapply HΦ
      unfold marshalRet
      ileft
      isplitr
      · ipureintro; rfl
      iexists bs
      iframe
    · iintro %s %err %Herr HΨ
      wp_auto
      iapply HΦ
      unfold marshalRet
      iright
      iframe
      ipureintro; exact Herr

end proof

end encoding.json
end Perennial
