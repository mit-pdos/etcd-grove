/-
The proof of `Spec/google_golang_org/grpc/createHeaderFields.lean`, over the grpc model's translated
body (`model_transport.go`).
-/
module

public import Spec.google_golang_org.grpc.createHeaderFields
public import Spec.google_golang_org.grpc.credentials.NewContextWithRequestInfo
public import Spec.google_golang_org.grpc.internal.grpcutil.RegisteredCompressors
public import Spec.google_golang_org.grpc.internal.grpcutil.ContentType
public import Spec.google_golang_org.grpc.internal.grpcutil.IsCompressorNameRegistered
public import Spec.google_golang_org.grpc.internal.grpcutil.EncodeDuration
public import Spec.google_golang_org.grpc.internal.metadata.ValidatePair
public import Spec.google_golang_org.grpc.internal.status.IsRestrictedControlPlaneCode
public import Spec.google_golang_org.grpc.status.FromError
public import Spec.google_golang_org.grpc.status.Errorf
public import Spec.google_golang_org.grpc.status.Error
public import Spec.google_golang_org.grpc.encodeMetadataHeader
public import Spec.google_golang_org.grpc.isReservedHeader
public import Spec.google_golang_org.grpc.metadata.fromOutgoingContextRaw
public import Spec.strconv.Itoa
public import Spec.strings.ToLower
public import Spec.strings.TrimSuffix
public import Spec.time.Until
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.Assumptions]

set_option hygiene false in
/-- One `headerFields = append(headerFields, headerField{...})`: the one-element literal, then the
append, on the slice `Hhf` with capacity `Hcap`. -/
local macro "append_hf" : tactic => `(tactic| (
  (try wp_auto)
  wp_bind (App (Val (GoInstruction (CompositeLiteral
    (go.SliceType google_golang_org.grpc.headerField.ty)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := google_golang_org.grpc.headerField)
    (t := google_golang_org.grpc.headerField.ty) [_]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lsl ⟨Hlsl, -⟩
  wp_apply wp_slice_append (V := google_golang_org.grpc.headerField) $$ [Hhf Hcap Hlsl]
    as %hsl ⟨Hhf, Hcap, -⟩
  · isplitl [Hhf]
    · iexact Hhf
    isplitl [Hcap]
    · iexact Hcap
    iexact Hlsl))

open github_com.mit_pdos.perennial.goose.model.strings in
theorem grpc.createHeaderFields.wp_proof
    (wp_NewContextWithRequestInfo : credentials.NewContextWithRequestInfo.spec (GF := GF) (hG := hG))
    (wp_RegisteredCompressors : grpcutil.RegisteredCompressors.spec (GF := GF) (hG := hG))
    (wp_ContentType : grpcutil.ContentType.spec (GF := GF) (hG := hG))
    (wp_IsCompressorNameRegistered : grpcutil.IsCompressorNameRegistered.spec (GF := GF) (hG := hG))
    (wp_EncodeDuration : grpcutil.EncodeDuration.spec (GF := GF) (hG := hG))
    (wp_ValidatePair : imetadata.ValidatePair.spec (GF := GF) (hG := hG))
    (wp_IsRestricted : istatus.IsRestrictedControlPlaneCode.spec (GF := GF) (hG := hG))
    (wp_FromError : status.FromError.spec (GF := GF) (hG := hG))
    (wp_Errorf : status.Errorf.spec (GF := GF) (hG := hG))
    (wp_Error : status.Error.spec (GF := GF) (hG := hG))
    (wp_encodeMetadataHeader : grpc.encodeMetadataHeader.spec (GF := GF) (hG := hG))
    (wp_isReservedHeader : grpc.isReservedHeader.spec (GF := GF) (hG := hG))
    (wp_fromOutgoingContextRaw : metadata.fromOutgoingContextRaw.spec (GF := GF) (hG := hG))
    (wp_Itoa : strconv.Itoa.spec (GF := GF) (hG := hG))
    (wp_ToLower : strings.ToLower.spec (GF := GF) (hG := hG))
    (wp_TrimSuffix : strings.TrimSuffix.spec (GF := GF) (hG := hG))
    (wp_Until : time.Until.spec (GF := GF) (hG := hG))
    (outRawFn_law : grpc.outRawFn.law (GF := GF) (hG := hG)) :
    grpc.createHeaderFields.spec (GF := GF) (hG := hG) := by
  intro ctx cc authInfo chp ch dq acc ua pcsl pcs dqc Ok Q R o hcreds
  wp_start as ⟨Hch, #Hacc, Hpf, Hpcs, Huf, #Hpcok, %HOk, HR, #Hdl, #Hout⟩
  ihave %Hchnn := typedPointsto_not_null $$ Hch
  iStructNamed Hch
  wp_auto
  wp_join iprop(∃ a : GoString, aud_ptr ↦ a ∗ callHdr_ptr ↦ chp ∗
      chp.[google_golang_org.grpc.callHdr, go!"Host"] ↦{dq} ch.Host' ∗
      chp.[google_golang_org.grpc.callHdr, go!"Method"] ↦{dq} ch.Method' ∗
      chp.[google_golang_org.grpc.callHdr, go!"Creds"] ↦{dq} ch.Creds')
    with [aud callHdr Host Method Creds] as ⟨%aud, aud, callHdr, Host, Method, Creds⟩
  · rw [hcreds]
    dsimp only
    wp_auto
    wp_join_done
  · clear Hif
    wp_apply wp_TrimSuffix
    generalize (if _ <:+ ch.Host' then _ else ch.Host') = hostv
    wp_apply wp_string_len as %HmL
    ihave IH : iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗ "pos" ∷ pos_ptr ↦ W64 (-1) ∗
        "%Hi" ∷ ⌜-1 ≤ sint.Z iv ∧ sint.Z iv < ch.Method'.length⌝) $$ [i pos]
    · iexists _
      simp only [named]
      iframe
      ipureintro
      constructor <;> word
    wp_for IH
    wp_if_destruct
    · have h0 : 0 ≤ sint.Z iv := by word
      obtain ⟨b, hb⟩ : ∃ b, ch.Method'[sint.nat iv]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by word)⟩
      rw [ite_eq_left h0, hb]
      wp_auto
      wp_if_destruct
      · wp_for_post
        rw [decide_eq_false (show iv ≠ W64 (-1) by intro h; subst h; simp at h0)]
        wp_auto
        have hb3 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z iv ∧
            sint.Z iv ≤ (ch.Method'.length : Int) := by
          refine ⟨by decide, by simpa using h0, by omega⟩
        rw [ite_eq_left hb3]
        wp_auto
        wp_join_done
      · wp_for_post
        iframe
        iexists iv - W64 1
        simp only [named]
        iframe
        ipureintro
        constructor <;> word
    · wp_apply wp_string_len as %-
      have hb3 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (ch.Method'.length : Int)) ∧
          sint.Z (W64 (ch.Method'.length : Int)) ≤ (ch.Method'.length : Int) := by
        refine ⟨by decide, ?_, ?_⟩ <;> word
      rw [ite_eq_left hb3]
      wp_auto
      wp_join_done
  wp_apply wp_NewContextWithRequestInfo as %c' ⟨#Hcv, #Hcd⟩
  ihave %Hpcsl := ownSlice_len _ _ _ $$ Hpcs
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ (am : Loc) (M : GMap GoString GoString)
          (cms : List (GMap GoString GoString)),
        authData_ptr ↦ am ∗ (⌜am = null ∧ M = ∅⌝ ∨ am ↦$ M) ∗
        ⌜cms.length = pcs.length ∧ (∀ cm ∈ cms, grpcHdr.credKeysOk cm) ∧
          ∀ k, M !! k = grpcHdr.credsLookup cms k⌝ ∗
        ([∗list] cm ∈ cms, □ Q cm) ∗ pcsl ↦*{dqc} pcs ∗ R ∗
        «$res0_ptr» ↦ zero_val GoSlice ∗ «$res1_ptr» ↦ GoInterface.nil) ∨
      (⌜v = returnVal #()⌝ ∗ ∃ (e : GoInterface) (sl : GoSlice), ⌜e ≠ GoInterface.nil⌝ ∗
        pcsl ↦*{dqc} pcs ∗ R ∗ «$res0_ptr» ↦ sl ∗ «$res1_ptr» ↦ e)))
    with [authData Hpcs HR «$res0» «$res1» perRPCCreds aud ctxWithRequestInfo]
  · have hp : pcs = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    ileft
    isplitr
    · itrivial
    iexists null, ∅, []
    iframe
    isplitl []
    · ileft; ipureintro; exact ⟨rfl, rfl⟩
    simp [hp, grpcHdr.credsLookup]
    isplitl [] <;> itrivial
  · wp_apply (wp_map_make1 (K := GoString) (V := GoString)) as %am Ham
    ihave IH : iprop(∃ (n : w64) (cv : GoInterface) (M : GMap GoString GoString)
        (cms : List (GMap GoString GoString)),
        "i" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ cv ∗ "Ham" ∷ am ↦$ M ∗ "HQ" ∷ ([∗list] cm ∈ cms, □ Q cm) ∗
        "HR" ∷ R ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ pcs.length ∧ cms.length = sint.nat n ∧
          (∀ cm ∈ cms, grpcHdr.credKeysOk cm) ∧ ∀ k, M !! k = grpcHdr.credsLookup cms k⌝)
      $$ [i c Ham HR]
    · iexists W64 0, GoInterface.nil, ∅, []
      simp only [named]
      iframe
      isplitl []
      · iapply (BigSepL.bigSepL_nil_intro (P := iprop(True)))
        itrivial
      ipureintro
      refine ⟨by decide, by simp, by simp; rfl, by simp, fun k => ?_⟩
      simp [grpcHdr.credsLookup]
    wp_for IH
    by_cases hlt : sint.Z n < sint.Z pcsl.len
    · rw [ite_eq_left (by simp [hlt])]
      have Hlt : sint.nat n < pcs.length := by
        obtain ⟨hl, _⟩ := Hpcsl; clear Hif; word
      obtain ⟨pc, Hpc⟩ : ∃ pc, pcs[sint.nat n]? = some pc := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z pcsl.len := ⟨Hn.1, hlt⟩
      wp_auto
      (try rw [ite_eq_left Hbnd])
      wp_apply wp_load_slice_index pcsl (sint.Z n) _ dqc pc Hn.1 $$ [$Hpcs] as Hpcs
      · ipureintro; exact Hpc
      ihave #Hpc1 := (BigSepL.bigSepL_lookup (Φ := fun _ pc => hdrCredsOk (GF := GF) pc Ok Q)
        Hpc) $$ Hpcok
      iunfold hdrCredsOk at Hpc1
      icases Hpc1 with ⟨%pci, %Hpci, #Hgrm⟩
      subst Hpci
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoString) (t := go.string) [aud]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      wp_auto
      wp_apply Hgrm $$ [HR] as %mp %err ⟨HR, Herr⟩
      · iframe; ipureintro; exact HOk
      icases Herr with (⟨%Hne, #Hse, %m, %c, #Hd, #Hc⟩ | ⟨%Heq, %cm, #Hcm, %Hck, #HQcm⟩)
      · -- the credentials' error
        obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
          cases err with
          | nil => exact absurd rfl Hne
          | ok e => exact ⟨e, rfl⟩
        dsimp only
        wp_auto
        wp_apply (wp_FromError (GoInterface.ok e) m c) $$ [$Hse $Hd $Hc]
          as %s %ok ⟨-, #Hcode, -, -, -⟩
        wp_if_destruct
        · -- not a status error: `Unauthenticated`
          wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
            (Val (LiteralValueV _)))
          iapply wp_slice_literal (V := GoInterface) (t := go.any) [GoInterface.ok e]
          wp_auto
          isplitl []
          · ipureintro; rfl
          iintro %asl2 -
          wp_apply (wp_Errorf (W32 16)) as %e2 %He2
          · ipureintro
            simp only [google_golang_org.grpc.codes.OK]
            exact fun h => absurd (go.intoVal_inj h) (by decide)
          wp_for_post
          iright
          isplitr
          · itrivial
          iexists e2, _
          iframe
          ipureintro; exact He2
        · wp_apply (wp_IsRestricted s c) $$ [Hcode]
          · iexact Hcode
          by_cases hr : c ∈ grpcHdr.restrictedCodes
          · rw [decide_eq_true hr]
            wp_auto
            wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
              (Val (LiteralValueV _)))
            iapply wp_slice_literal (V := GoInterface) (t := go.any) [GoInterface.ok e]
            wp_auto
            isplitl []
            · ipureintro; rfl
            iintro %asl2 -
            wp_apply (wp_Errorf (W32 13)) as %e2 %He2
            · ipureintro
              simp only [google_golang_org.grpc.codes.OK]
              exact fun h => absurd (go.intoVal_inj h) (by decide)
            wp_for_post
            iright
            isplitr
            · itrivial
            iexists e2, _
            iframe
            ipureintro; exact He2
          · rw [decide_eq_false hr]
            wp_auto
            wp_for_post
            iright
            isplitr
            · itrivial
            iexists GoInterface.ok e, _
            iframe
            ipureintro; exact Hne
      · -- the credentials' map
        subst Heq
        dsimp only
        wp_auto
        iunfold credsMapAt at Hcm
        icases Hcm with (%Hnull | #Hcm)
        · obtain ⟨rfl, rfl⟩ := Hnull
          wp_call
          wp_for_post
          iframe Hpcs «$res0» «$res1» aud ctxWithRequestInfo authData
          iexists n + W64 1, GoInterface.ok pci, M, cms ++ [∅]
          simp only [named]
          iframe
          isplitl []
          · iapply BigSepL.bigSepL_singleton.2
            iexact HQcm
          ipureintro
          refine ⟨by word, by word, by simp; word, ?_, fun k => ?_⟩
          · intro cm hm
            rcases List.mem_append.1 hm with hm | hm
            · exact Hn.2.2.2.1 cm hm
            · simp at hm; subst hm; exact Hck
          · rw [grpcHdr.credsLookup_snoc, ← Hn.2.2.2.2 k]; simp
        · wp_apply (wp_map_for_range (K := GoString) (V := GoString) (fun keys (j : Int) => iprop(
              ∃ (Mi : GMap GoString GoString) (kv vv : GoString),
              "k" ∷ k_ptr ↦ kv ∗ "v" ∷ v_ptr ↦ vv ∗ "Ham" ∷ am ↦$ Mi ∗
              "authData" ∷ authData_ptr ↦ am ∗ "HR" ∷ R ∗ "Hpcs" ∷ pcsl ↦*{dqc} pcs ∗
              "«$res0»" ∷ «$res0_ptr» ↦ zero_val GoSlice ∗
              "«$res1»" ∷ «$res1_ptr» ↦ GoInterface.nil ∗
              "%HMi" ∷ ⌜0 ≤ j ∧ ∀ k, Mi !! k =
                (if k ∈ keys.take j.toNat then cm !! k else none).or (M !! k)⌝))) $$ Hcm
          iintro %keys ⟨%Hmem, %Hsize, %Hnd⟩
          isplitl [k v Ham authData HR Hpcs «$res0» «$res1»]
          · iexists M, zero_val GoString, zero_val GoString
            simp only [named]
            iframe
            ipureintro
            refine ⟨by omega, fun k => ?_⟩
            simp
          isplitr
          · imodintro
            iintro %j %key %vl ⟨%Hk, %Hlook⟩ ⟨%Mi, %kv, %vv, k, v, Ham, authData, HR, Hpcs,
              «$res0», «$res1», %HMi⟩
            wp_auto
            wp_apply wp_ToLower as %r %Hr
            have hkey := (Hck key vl Hlook).1
            obtain rfl : r = key := (Hr key hkey).2 (grpcHdr.lowersTo_self key)
            wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
              (Val (LiteralValueV _)))
            iapply wp_slice_literal (V := GoString) (t := go.string) [vl]
            wp_auto
            isplitl []
            · ipureintro; rfl
            iintro %vsl ⟨Hvsl, -⟩
            wp_apply (wp_ValidatePair r _ [vl] (DFrac.own 1)) $$ [$Hvsl] as %ve ⟨Hvsl, %Hve, #Hvf⟩
            cases ve with
            | nil =>
              dsimp only
              wp_auto
              wp_apply (wp_mapInsert go.string am Mi r vl) $$ [$Ham] as Ham
              unfold forMapPostcondition
              iright; ileft
              isplitr
              · itrivial
              iexists _, r, vl
              simp only [named]
              iframe
              ipureintro
              refine ⟨by omega, fun k => ?_⟩
              have htake : keys.take (j + 1).toNat = keys.take j.toNat ++ [r] := by
                rw [show (j + 1).toNat = j.toNat + 1 by omega, List.take_add_one, Hk]; rfl
              rw [htake]
              by_cases hkr : k = r
              · subst hkr; simp [Hlook]
              · have h2 := HMi.2 k
                simp [hkr, Ne.symm hkr, h2]
            | ok vi =>
              dsimp only
              wp_auto
              ihave #Hvf' := fmtErrorOkOrNil_ne (GoInterface.ok vi) (by simp) $$ Hvf
              iunfold fmtErrorOk at Hvf'
              icases Hvf' with ⟨-, #Hstr⟩
              iunfold fmt.stringMethodSpec at Hstr
              wp_apply Hstr as %emsg
              wp_apply (wp_Error (W32 13) emsg) as %e3 ⟨%He3, -⟩
              · ipureintro
                simp only [google_golang_org.grpc.codes.OK]
                exact fun h => absurd (go.intoVal_inj h) (by decide)
              unfold forMapPostcondition
              iright; iright; iright; ileft
              iexists #()
              isplitr
              · itrivial
              iintro -
              wp_for_post
              iright
              isplitr
              · itrivial
              iexists e3, _
              iframe
              ipureintro; exact He3
          · iintro ⟨%Mi, %kv, %vv, k, v, Ham, authData, HR, Hpcs, «$res0», «$res1», %HMi⟩ -
            wp_for_post
            iframe Hpcs «$res0» «$res1» aud ctxWithRequestInfo authData
            iexists n + W64 1, GoInterface.ok pci, Mi, cms ++ [cm]
            simp only [named]
            iframe
            isplitl []
            · iapply BigSepL.bigSepL_singleton.2
              iexact HQcm
            ipureintro
            refine ⟨by word, by word, by simp; word, ?_, fun k => ?_⟩
            · intro cm' hm
              rcases List.mem_append.1 hm with hm | hm
              · exact Hn.2.2.2.1 cm' hm
              · simp at hm; subst hm; exact Hck
            · rw [HMi.2 k, grpcHdr.credsLookup_snoc, ← Hn.2.2.2.2 k]
              have htk : keys.take (GMap.size cm : Int).toNat = keys := by
                apply List.take_of_length_le; rw [Hsize]; simp
              rw [htk]
              by_cases hk : k ∈ keys
              · simp [hk]
              · have : cm !! k = none := by
                  cases h : cm !! k with
                  | none => rfl
                  | some _ => exact absurd ((Hmem k).2 (by simp [h])) hk
                simp [hk, this]
    · have hn : sint.nat n = pcs.length := by
        obtain ⟨_, hle, _⟩ := Hn; obtain ⟨hl, _⟩ := Hpcsl; word
      rw [ite_eq_right (by simp [hlt]), ite_eq_right (by simp [hlt])]
      ileft
      isplitr
      · itrivial
      iexists am, M, cms
      iframe
      ipureintro
      exact ⟨by omega, Hn.2.2.2.1, Hn.2.2.2.2⟩
  iintro (⟨%Hv, %am, %M, %cms, authData, Ham, %HM, HQ, Hpcs, HR, «$res0», «$res1»⟩ |
    ⟨%Hv, %e, %sl, %He, Hpcs, HR, «$res0», «$res1»⟩)
  rotate_left
  · subst Hv
    wp_auto
    ihave Hch : chp ↦{dq} ch $$ [Host Method SendCompress AcceptedCompressors Creds ContentSubtype
      PreviousAttempts Authority]
    · iapply typedPointsto_combine _ _ _ Hchnn
      simp only [TypedPointsto.typedPointstoDef, named]
      iframe
    iapply HΦ
    iframe
    iright
    ipureintro; exact He
  subst Hv
  wp_auto
  rw [hcreds]
  dsimp only
  wp_auto
  wp_apply wp_RegisteredCompressors
  wp_join iprop(registeredCompressors_ptr ↦ acc ∗ callHdr_ptr ↦ chp ∗
      chp.[google_golang_org.grpc.callHdr, go!"AcceptedCompressors"] ↦{dq} ch.AcceptedCompressors')
    with [registeredCompressors callHdr AcceptedCompressors]
    as ⟨registeredCompressors, callHdr, AcceptedCompressors⟩
  · icases Hacc with (%Hacc | #Hacc)
    · obtain ⟨-, rfl⟩ := Hacc
      iframe
    · ihave %h := typedPointsto_not_null _ _ _ $$ Hacc
      exact absurd Hif h
  · icases Hacc with (%Hacc | #Hacc)
    · exact absurd Hacc.1 Hif
    · wp_auto
      wp_join_done
  ihave Hhf := ownSlice_nil (V := google_golang_org.grpc.headerField) (DFrac.own 1)
  ihave Hcap := ownSliceCap_nil (V := google_golang_org.grpc.headerField)
  rw [show (zero_val GoSlice) = slice.nil from rfl]
  append_hf
  append_hf
  append_hf
  append_hf
  wp_apply wp_ContentType
  append_hf
  append_hf
  append_hf
  wp_join iprop(∃ (hsl : GoSlice) (fs : List google_golang_org.grpc.headerField),
      headerFields_ptr ↦ hsl ∗ hsl ↦* fs ∗
      ownSliceCap google_golang_org.grpc.headerField hsl (DFrac.own 1) ∗
      ⌜hfPairs fs = grpcHdr.baseFields ch.Method' ch.Host' ch.ContentSubtype' ua ++
        grpcHdr.prevFields ch.PreviousAttempts'⌝ ∗
      callHdr_ptr ↦ chp ∗
      chp.[google_golang_org.grpc.callHdr, go!"PreviousAttempts"] ↦{dq} ch.PreviousAttempts')
    with [headerFields Hhf Hcap callHdr PreviousAttempts]
    as ⟨%hsl1, %fs1, headerFields, Hhf, Hcap, %Hfs1, callHdr, PreviousAttempts⟩
  · wp_apply wp_Itoa as %istr %Histr
    append_hf
    isplitr
    · itrivial
    iexists _, _
    iframe
    ipureintro
    subst Histr
    have hpos : 0 < sint.Z ch.PreviousAttempts' := by simpa using Hif
    simp [hfPairs, grpcHdr.baseFields, grpcHdr.prevFields, hpos]
  · iexists _, _
    iframe
    ipureintro
    have hpos : ¬ 0 < sint.Z ch.PreviousAttempts' := by simpa using Hif
    simp [hfPairs, grpcHdr.baseFields, grpcHdr.prevFields, hpos]
  wp_join iprop(∃ (hsl : GoSlice) (fs : List google_golang_org.grpc.headerField),
      headerFields_ptr ↦ hsl ∗ hsl ↦* fs ∗
      ownSliceCap google_golang_org.grpc.headerField hsl (DFrac.own 1) ∗
      ⌜hfPairs fs = grpcHdr.baseFields ch.Method' ch.Host' ch.ContentSubtype' ua ++
        grpcHdr.prevFields ch.PreviousAttempts' ++ grpcHdr.encFields ch.SendCompress'⌝ ∗
      registeredCompressors_ptr ↦ grpcHdr.regCompOf acc ch.SendCompress' ∗
      callHdr_ptr ↦ chp ∗
      chp.[google_golang_org.grpc.callHdr, go!"SendCompress"] ↦{dq} ch.SendCompress')
    with [headerFields Hhf Hcap callHdr SendCompress registeredCompressors]
    as ⟨%hsl2, %fs2, headerFields, Hhf, Hcap, %Hfs2, registeredCompressors, callHdr, SendCompress⟩
  · iexists _, _
    iframe
    isplitl []
    · ipureintro
      simp only [hfPairs] at Hfs1 ⊢
      simp [Hfs1, grpcHdr.encFields, Hif]
    simp only [grpcHdr.regCompOf, Hif, ↓reduceIte]
    iframe
  · append_hf
    wp_apply wp_IsCompressorNameRegistered
    by_cases hacc : acc = []
    · subst hacc
      wp_auto
      isplitr
      · itrivial
      iexists _, _
      iframe
      isplitl []
      · ipureintro
        simp only [hfPairs] at Hfs1 ⊢
        simp [Hfs1, grpcHdr.encFields, Hif]
      simp [grpcHdr.regCompOf, Hif]
      iframe
    · rw [decide_eq_false hacc]
      wp_auto
      isplitr
      · itrivial
      iexists _, _
      iframe
      isplitl []
      · ipureintro
        simp only [hfPairs] at Hfs1 ⊢
        simp [Hfs1, grpcHdr.encFields, Hif]
      simp [grpcHdr.regCompOf, Hif, hacc]
      iframe
  sorry

end proof

end EtcdGrove
end Perennial
