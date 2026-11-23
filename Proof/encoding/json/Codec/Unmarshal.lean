/-
The proof of `Unmarshal` (`Spec/encoding/json/Codec/Unmarshal.lean`): the comma-ok assertion decides
the route as `unmarshalVia` does; a method route calls the method value `unmarshalAt` is about; the
codec route finds the registered codec (`getCodec`), checks validity (`valid`, over its `Scan`), and
on valid JSON calls its `Unmarshal` under `unmarshalOk`, else returns a fresh `*SyntaxError`.
-/
module

public import Spec.encoding.json.Codec.Unmarshal
public import Spec.encoding.json.Codec.getCodec
public import Spec.encoding.json.Codec.valid

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

theorem Unmarshal.wp_proof (wp_getCodec : getCodec.spec (GF := GF) (hG := hG))
    (wp_valid : valid.spec (GF := GF) (hG := hG)) :
    Unmarshal.spec (GF := GF) (hG := hG) := by
  intro J F data dq bs ptr Ψ
  rcases ptr with ⟨ty, x⟩ | _
  · cases h1 : go.typeSetContains ty encoding.json.modelUnmarshaler.ty
    · simp only [unmarshalVia, h1, Bool.false_eq_true, ↓reduceIte]
      wp_start as ⟨Hroute, Hs, Hdec⟩
      wp_auto
      try simp only [h1, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      unfold codecRoute
      icases Hroute with ⟨%fm, %fu, #Hset, #Hok⟩
      wp_apply wp_getCodec fm fu $$ Hset as %c #Hc
      unfold codecFnsWith
      icases Hc with ⟨#HM, #HU, #HS⟩
      unfold codecOkWith
      icases Hok with ⟨-, #HuOk, #Hscan⟩
      try wp_auto
      wp_apply wp_valid F c data dq bs $$ [$HS $Hscan $Hs] as Hs
      by_cases hv : models_lab.jsoncodec.jsonValid F bs
      · rw [decide_eq_true hv]
        wp_auto
        unfold models_lab.jsoncodec.unmarshalOk
        wp_bind (App (App (Val #fu) _) _)
        iapply HuOk $$ %data %dq %bs %_ %Ψ %_ %hv Hs Hdec
        inext
        iintro %err %ok Hs %Hok HΨ
        wp_auto
        iapply HΦ
        iframe Hs
        unfold unmarshalRet
        ileft
        isplitr
        · ipureintro; exact hv
        iexists ok
        iframe HΨ
        ipureintro; exact Hok
      · rw [decide_eq_false hv]
        wp_auto
        wp_alloc e as He
        wp_auto
        iapply HΦ
        iframe Hs
        unfold unmarshalRet
        iright
        iframe Hdec
        ipureintro
        exact ⟨hv, by simp⟩
    · simp only [unmarshalVia, h1, ↓reduceIte]
      wp_start as ⟨⟨#Hscan, Hm⟩, Hs, Hdec⟩
      wp_auto
      try simp only [h1, ↓reduceIte]
      wp_auto
      unfold unmarshalAt
      wp_bind (App (App (Val #(methods _ _ _)) _) _)
      iapply Hm $$ Hs Hdec
      inext
      iintro %err Hs Hret
      wp_auto
      iapply HΦ
      iframe Hs
      unfold unmarshalRet
      iexact Hret
  · simp only [unmarshalVia]
    wp_start as ⟨Hroute, Hs, Hdec⟩
    wp_auto
    unfold codecRoute
    icases Hroute with ⟨%fm, %fu, #Hset, #Hok⟩
    wp_apply wp_getCodec fm fu $$ Hset as %c #Hc
    unfold codecFnsWith
    icases Hc with ⟨#HM, #HU, #HS⟩
    unfold codecOkWith
    icases Hok with ⟨-, #HuOk, #Hscan⟩
    try wp_auto
    wp_apply wp_valid F c data dq bs $$ [$HS $Hscan $Hs] as Hs
    by_cases hv : models_lab.jsoncodec.jsonValid F bs
    · rw [decide_eq_true hv]
      wp_auto
      unfold models_lab.jsoncodec.unmarshalOk
      wp_bind (App (App (Val #fu) _) _)
      iapply HuOk $$ %data %dq %bs %_ %Ψ %_ %hv Hs Hdec
      inext
      iintro %err %ok Hs %Hok HΨ
      wp_auto
      iapply HΦ
      iframe Hs
      unfold unmarshalRet
      ileft
      isplitr
      · ipureintro; exact hv
      iexists ok
      iframe HΨ
      ipureintro; exact Hok
    · rw [decide_eq_false hv]
      wp_auto
      wp_alloc e as He
      wp_auto
      iapply HΦ
      iframe Hs
      unfold unmarshalRet
      iright
      iframe Hdec
      ipureintro
      exact ⟨hv, by simp⟩

end proof

end encoding.json
end Perennial
