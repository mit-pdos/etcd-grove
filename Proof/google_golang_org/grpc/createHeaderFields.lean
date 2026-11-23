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
variable [ctx_sem : _root_.Perennial.context.Assumptions]

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
  irename : ("_" ∷ True : IProp GF) => Htriv
  iclear Htriv
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
  ihave Hhf0 := ownSlice_nil (V := google_golang_org.grpc.headerField) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := google_golang_org.grpc.headerField)
  rw [show (zero_val GoSlice) = slice.nil from rfl]
  wp_bind (App (Val (GoInstruction (CompositeLiteral
    (go.SliceType google_golang_org.grpc.headerField.ty)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := google_golang_org.grpc.headerField)
    (t := google_golang_org.grpc.headerField.ty) [_]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lsl ⟨Hlsl, -⟩
  wp_apply wp_slice_append (V := google_golang_org.grpc.headerField) $$ [Hhf0 Hcap0 Hlsl]
    as %hsl ⟨Hhf, Hcap, -⟩
  · isplitl [Hhf0]
    · iexact Hhf0
    isplitl [Hcap0]
    · iexact Hcap0
    iexact Hlsl
  iclear Hhf0 Hcap0
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
  wp_join iprop(∃ (hsl : GoSlice) (fs : List google_golang_org.grpc.headerField),
      headerFields_ptr ↦ hsl ∗ hsl ↦* fs ∗
      ownSliceCap google_golang_org.grpc.headerField hsl (DFrac.own 1) ∗
      ⌜hfPairs fs = grpcHdr.callHdrFields ch acc ua⌝)
    with [headerFields Hhf Hcap registeredCompressors]
    as ⟨%hsl3, %fs3, headerFields, Hhf, Hcap, %Hfs3⟩
  · iexists _, _
    iframe
    ipureintro
    simp only [hfPairs] at Hfs2 ⊢
    simp [Hfs2, grpcHdr.callHdrFields, grpcHdr.acceptFields, Hif]
  · append_hf
    isplitr
    · itrivial
    iexists _, _
    iframe
    ipureintro
    simp only [hfPairs] at Hfs2 ⊢
    simp [Hfs2, grpcHdr.callHdrFields, grpcHdr.acceptFields, Hif]
  iunfold ctxDeadline at Hdl
  wp_apply Hdl as %dl %dok
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ (hsl : GoSlice) (fs : List google_golang_org.grpc.headerField)
          (tfs : List (GoString × GoString)),
        headerFields_ptr ↦ hsl ∗ hsl ↦* fs ∗
        ownSliceCap google_golang_org.grpc.headerField hsl (DFrac.own 1) ∗
        ⌜hfPairs fs = grpcHdr.callHdrFields ch acc ua ++ tfs ∧ grpcHdr.timeoutFieldsOk tfs⌝ ∗
        «$res0_ptr» ↦ slice.nil ∗ «$res1_ptr» ↦ GoInterface.nil) ∨
      (⌜v = returnVal #()⌝ ∗ ∃ (e : GoInterface) (sl : GoSlice), ⌜e ≠ GoInterface.nil⌝ ∗
        «$res0_ptr» ↦ sl ∗ «$res1_ptr» ↦ e)))
    with [headerFields Hhf Hcap «$res0» «$res1» dl]
  · ileft
    isplitr
    · itrivial
    iexists _, _, []
    iframe
    ipureintro
    exact ⟨by simp [Hfs3], Or.inl rfl⟩
  · wp_apply wp_Until as %d -
    wp_if_destruct
    · -- the deadline has passed
      ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
      · iPkgInit
      ihave #Hci : (_root_.Perennial.context.isInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hctxp
      icases Hci with ⟨-, -, -, -, -, -, #Hdv, -⟩
      wp_auto
      iclear Hdl Hcv Hcd
      wp_method_call; wp_call
      wp_auto
      wp_apply (wp_Error (W32 4)) as %e4 ⟨%He4, -⟩
      · ipureintro
        simp only [google_golang_org.grpc.codes.OK]
        exact fun h => absurd (go.intoVal_inj h) (by decide)
      iright
      isplitr
      · itrivial
      iexists e4, _
      iframe
      ipureintro; exact He4
    · wp_apply wp_EncodeDuration
      append_hf
      ileft
      isplitr
      · itrivial
      iexists _, _, [(go!"grpc-timeout", grpcHdr.encodeDurationOf d)]
      iframe
      ipureintro
      refine ⟨?_, Or.inr ⟨d, by simpa using Hif, rfl⟩⟩
      simp only [hfPairs] at Hfs3 ⊢
      simp [Hfs3]
  iintro (⟨%Hv, %hsl4, %fs4, %tfs, headerFields, Hhf, Hcap, %Hfs4, «$res0», «$res1»⟩ |
    ⟨%Hv, %e, %sl, %He, «$res0», «$res1»⟩)
  rotate_left
  · subst Hv
    wp_auto
    ihave Hch : chp ↦{dq} ch $$ [Host Method SendCompress AcceptedCompressors Creds ContentSubtype
      PreviousAttempts Authority]
    · iapply typedPointsto_combine _ _ _ Hchnn
      simp only [TypedPointsto.typedPointstoDef, named]
      rw [hcreds]
      iframe
    iapply HΦ
    iframe
    iright
    ipureintro; exact He
  subst Hv
  wp_auto
  wp_join iprop(∃ (hsl : GoSlice) (fs : List google_golang_org.grpc.headerField)
      (afs : List (GoString × GoString)),
      headerFields_ptr ↦ hsl ∗ hsl ↦* fs ∗
      ownSliceCap google_golang_org.grpc.headerField hsl (DFrac.own 1) ∗
      ⌜hfPairs fs = grpcHdr.callHdrFields ch acc ua ++ tfs ++ afs ∧
        grpcHdr.credsFieldsOk cms afs⌝) at next
    with [headerFields Hhf Hcap Ham k v]
    as ⟨%hsl5, %fs5, %afs, headerFields, Hhf, Hcap, %Hfs5⟩
  · icases Ham with (%Hnull | Ham)
    · obtain ⟨rfl, rfl⟩ := Hnull
      wp_call
      isplitr
      · itrivial
      iexists _, _, []
      iframe
      ipureintro
      refine ⟨by simp [Hfs4.1], [], ⟨List.nodup_nil, fun k => ?_⟩, rfl⟩
      rw [← HM.2.2 k]; simp
    · wp_apply (wp_map_for_range (K := GoString) (V := GoString) (fun keys (j : Int) => iprop(
          ∃ (hsl : GoSlice) (fs : List google_golang_org.grpc.headerField) (kv vv : GoString),
          "headerFields" ∷ headerFields_ptr ↦ hsl ∗ "Hhf" ∷ hsl ↦* fs ∗
          "Hcap" ∷ ownSliceCap google_golang_org.grpc.headerField hsl (DFrac.own 1) ∗
          "k" ∷ k_ptr ↦ kv ∗ "v" ∷ v_ptr ↦ vv ∗
          "%Hfj" ∷ ⌜0 ≤ j ∧ hfPairs fs = grpcHdr.callHdrFields ch acc ua ++ tfs ++
            grpcHdr.mapFields (keys.take j.toNat) (M !! ·)⌝))) $$ Ham
      iintro %keys ⟨%Hmem, %Hsize, %Hnd⟩
      isplitl [headerFields Hhf Hcap k v]
      · iexists _, _, _, _
        simp only [named]
        iframe
        ipureintro
        refine ⟨by omega, ?_⟩
        simp [Hfs4.1, grpcHdr.mapFields]
      isplitr
      · imodintro
        iintro %j %key %vl ⟨%Hk, %Hlook⟩ ⟨%hsl, %fs, %kv, %vv, headerFields, Hhf, Hcap, k, v, %Hfj⟩
        wp_auto
        wp_apply wp_encodeMetadataHeader
        append_hf
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · itrivial
        iexists _, _, key, vl
        simp only [named]
        iframe
        ipureintro
        refine ⟨by omega, ?_⟩
        have htake : keys.take (j + 1).toNat = keys.take j.toNat ++ [key] := by
          rw [show (j + 1).toNat = j.toNat + 1 by omega, List.take_add_one, Hk]; rfl
        rw [htake, grpcHdr.mapFields_snoc _ _ _ vl Hlook]
        simp only [hfPairs] at Hfj ⊢
        simp [Hfj.2]
      · iintro ⟨%hsl, %fs, %kv, %vv, headerFields, Hhf, Hcap, k, v, %Hfj⟩ Ham
        isplitr
        · itrivial
        iexists _, _, _
        iframe
        ipureintro
        have htk : keys.take (GMap.size M : Int).toNat = keys := by
          apply List.take_of_length_le; rw [Hsize]; simp
        rw [htk] at Hfj
        refine ⟨Hfj.2, keys, ⟨Hnd, fun k => ?_⟩, ?_⟩
        · rw [← HM.2.2 k]; exact Hmem k
        · simp only [grpcHdr.mapFields]
          congr 1; funext k; rw [HM.2.2 k]
  wp_call
  wp_auto
  ihave #Hfn := outRawFn_law $$ Hpkg
  iunfold outRawIs at Hout
  icases Hout with ⟨%vo, #Hval, Ho⟩
  wp_auto
  rcases o with _ | ⟨Mo, rows⟩
  · -- no `rawMD`: no outgoing fields
    icases Ho with %Ho
    wp_apply (wp_fromOutgoingContextRaw ctx vo none Ho) $$ [Hval] as %mdl %addl %okr %Hokr
    · iexact Hval
    simp only at Hokr
    subst Hokr
    wp_auto
    ihave Hch : chp ↦{dq} ch $$ [Host Method SendCompress AcceptedCompressors Creds ContentSubtype
      PreviousAttempts Authority]
    · iapply typedPointsto_combine _ _ _ Hchnn
      simp only [TypedPointsto.typedPointstoDef, named]
      rw [hcreds]
      iframe
    iapply HΦ
    iframe
    ileft
    isplitr
    · itrivial
    iexists fs5, cms, tfs, afs, []
    iframe
    ipureintro
    exact ⟨by simp [Hfs5.1], Hfs4.2, HM.1, HM.2.1, Hfs5.2, rfl⟩
  · icases Ho with ⟨%r, %ms, %rsl, %Hvo, #Hmd, %Hdom, #Hms, #Had, %Hrows, #Hrs⟩
    wp_apply (wp_fromOutgoingContextRaw ctx vo (some r) Hvo) $$ [Hval] as %mdl %addl %okr %Hokr
    · iexact Hval
    obtain ⟨rfl, rfl, rfl⟩ := Hokr
    wp_auto
    -- the map's fields
    wp_join iprop(∃ (hsl : GoSlice) (fs : List google_golang_org.grpc.headerField)
        (mkeys : List GoString),
        headerFields_ptr ↦ hsl ∗ hsl ↦* fs ∗
        ownSliceCap google_golang_org.grpc.headerField hsl (DFrac.own 1) ∗
        ⌜grpcHdr.enumKeys (Mo !! ·) mkeys ∧
          hfPairs fs = grpcHdr.callHdrFields ch acc ua ++ tfs ++ afs ++
            mkeys.flatMap (fun k => grpcHdr.mdKeyFields k ((Mo !! k).getD []))⌝) at next
      with [headerFields Hhf Hcap vv k]
      as ⟨%hsl6, %fs6, %mkeys, headerFields, Hhf, Hcap, %Hfs6⟩
    · icases Hmd with (%Hnull | #Hmd)
      · obtain ⟨hmd, rfl⟩ := Hnull
        rw [hmd]
        wp_call
        isplitr
        · itrivial
        iexists _, _, []
        iframe
        ipureintro
        refine ⟨⟨List.nodup_nil, fun k => ?_⟩, by simp [Hfs5.1]⟩
        have := Hdom k
        simp only [List.not_mem_nil, false_iff]
        intro h
        rw [this] at h
        simp at h
      · wp_apply (wp_map_for_range (K := GoString) (V := GoSlice) (fun keys (j : Int) => iprop(
            ∃ (hsl : GoSlice) (fs : List google_golang_org.grpc.headerField) (kv : GoString)
              (vvv : GoSlice),
            "headerFields" ∷ headerFields_ptr ↦ hsl ∗ "Hhf" ∷ hsl ↦* fs ∗
            "Hcap" ∷ ownSliceCap google_golang_org.grpc.headerField hsl (DFrac.own 1) ∗
            "k" ∷ k_ptr ↦ kv ∗ "vv" ∷ vv_ptr ↦ vvv ∗
            "%Hfj" ∷ ⌜0 ≤ j ∧ hfPairs fs = grpcHdr.callHdrFields ch acc ua ++ tfs ++ afs ++
              (keys.take j.toNat).flatMap
                (fun k => grpcHdr.mdKeyFields k ((Mo !! k).getD []))⌝))) $$ Hmd
        iintro %keys ⟨%Hmem, %Hsize, %Hnd⟩
        isplitl [headerFields Hhf Hcap k vv]
        · iexists _, _, _, _
          simp only [named]
          iframe
          ipureintro
          refine ⟨by omega, ?_⟩
          simp [Hfs5.1]
        isplitr
        · imodintro
          iintro %j %key %slv ⟨%Hk, %Hlook⟩ ⟨%hsl, %fs, %kv, %vvv, headerFields, Hhf, Hcap, k, vv, %Hfj⟩
          wp_auto
          wp_apply wp_isReservedHeader
          have htake : keys.take (j + 1).toNat = keys.take j.toNat ++ [key] := by
            rw [show (j + 1).toNat = j.toNat + 1 by omega, List.take_add_one, Hk]; rfl
          by_cases hres : grpcHdr.reservedHdr key
          · rw [decide_eq_true hres]
            wp_auto
            unfold forMapPostcondition
            ileft
            isplitr
            · itrivial
            iexists _, _, key, slv
            simp only [named]
            iframe
            ipureintro
            refine ⟨by omega, ?_⟩
            rw [htake, List.flatMap_append, Hfj.2]
            simp [grpcHdr.mdKeyFields, hres]
          · rw [decide_eq_false hres]
            wp_auto
            ihave #Hsl := (BigSepM.bigSepM_lookup (Φ := fun k sl => iprop(sl ↦*□ ((Mo !! k).getD [])))
              Hlook) $$ Hms
            ihave %Hslen := ownSlice_len _ _ _ $$ Hsl
            ihave IH : iprop(∃ (n : w64) (vx : GoString) (hsl' : GoSlice)
                (fs' : List google_golang_org.grpc.headerField),
                "i" ∷ i_ptr ↦ n ∗ "v" ∷ v_ptr ↦ vx ∗ "headerFields" ∷ headerFields_ptr ↦ hsl' ∗
                "Hhf" ∷ hsl' ↦* fs' ∗
                "Hcap" ∷ ownSliceCap google_golang_org.grpc.headerField hsl' (DFrac.own 1) ∗
                "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ((Mo !! key).getD []).length ∧
                  hfPairs fs' = hfPairs fs ++ ((((Mo !! key).getD []).take (sint.nat n)).map
                    fun v => (key, grpcHdr.encMdHdr key v))⌝) $$ [i v headerFields Hhf Hcap]
            · iexists W64 0, _, _, _
              simp only [named]
              iframe
              ipureintro
              refine ⟨by decide, by simp, ?_⟩
              simp
            wp_for IH
            by_cases hlt : sint.Z n < sint.Z slv.len
            · rw [ite_eq_left (by simp [hlt])]
              have Hlt : sint.nat n < ((Mo !! key).getD []).length := by
                obtain ⟨hl, _⟩ := Hslen; word
              obtain ⟨x, Hx⟩ : ∃ x, ((Mo !! key).getD [])[sint.nat n]? = some x :=
                ⟨_, List.getElem?_eq_getElem Hlt⟩
              have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z slv.len := ⟨Hn.1, hlt⟩
              wp_auto
              (try rw [ite_eq_left Hbnd])
              wp_apply wp_load_slice_index slv (sint.Z n) _ DFrac.discard x Hn.1 $$ [$Hsl] as -
              · ipureintro; exact Hx
              wp_apply wp_encodeMetadataHeader
              append_hf
              wp_for_post
              iframe
              iexists n + W64 1, x, _, _
              simp only [named]
              iframe
              ipureintro
              have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
              refine ⟨by word, by rw [hn1]; omega, ?_⟩
              rw [hn1, List.take_add_one, Hx]
              simp only [hfPairs] at Hn ⊢
              simp [Hn.2.2]
            · have hn : sint.nat n = ((Mo !! key).getD []).length := by
                obtain ⟨hl, _⟩ := Hslen; obtain ⟨_, hle, _⟩ := Hn; word
              rw [ite_eq_right (by simp [hlt]), ite_eq_right (by simp [hlt])]
              unfold forMapPostcondition
              iright; ileft
              isplitr
              · itrivial
              iexists _, _, key, slv
              simp only [named]
              iframe
              ipureintro
              refine ⟨by omega, ?_⟩
              rw [htake, List.flatMap_append, Hn.2.2, Hfj.2, hn, List.take_length]
              simp [grpcHdr.mdKeyFields, hres]
        · iintro ⟨%hsl, %fs, %kv, %vvv, headerFields, Hhf, Hcap, k, vv, %Hfj⟩ Hmd'
          isplitr
          · itrivial
          iexists _, _, keys
          iframe
          ipureintro
          have htk : keys.take (GMap.size ms : Int).toNat = keys := by
            apply List.take_of_length_le; rw [Hsize]; simp
          rw [htk] at Hfj
          refine ⟨⟨Hnd, fun k => ?_⟩, Hfj.2⟩
          rw [Hmem k, Hdom k]
    -- the added rows' fields
    rename_i kout _
    ihave %Hrsl := ownSlice_len _ _ _ $$ Had
    ihave IH : iprop(∃ (m : w64) (kk : GoString) (vvx : GoSlice) (hsl' : GoSlice)
        (fs' : List google_golang_org.grpc.headerField),
        "i" ∷ i_ptr ↦ m ∗ "k" ∷ kout ↦ kk ∗ "vv" ∷ vv_ptr ↦ vvx ∗
        "headerFields" ∷ headerFields_ptr ↦ hsl' ∗ "Hhf" ∷ hsl' ↦* fs' ∗
        "Hcap" ∷ ownSliceCap google_golang_org.grpc.headerField hsl' (DFrac.own 1) ∗
        "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.nat m ≤ rows.length ∧
          hfPairs fs' = hfPairs fs6 ++ (rows.take (sint.nat m)).flatMap grpcHdr.rowFields⌝)
      $$ [i k vv headerFields Hhf Hcap]
    · iexists W64 0, _, _, _, _
      simp only [named]
      iframe
      ipureintro
      rw [show sint.nat (W64 0) = 0 by decide]
      refine ⟨by decide, by omega, by simp⟩
    iclear Hmd Hms Hfn Hval
    wp_for IH
    by_cases hlt : sint.Z m < sint.Z r.added'.len
    · rw [ite_eq_left (by simp [hlt])]
      sorry
    · have hm : sint.nat m = rows.length := by
        obtain ⟨hl, _⟩ := Hrsl; obtain ⟨_, hle, _⟩ := Hm; word
      rw [ite_eq_right (by simp [hlt]), ite_eq_right (by simp [hlt])]
      wp_auto
      ihave Hch : chp ↦{dq} ch $$ [Host Method SendCompress AcceptedCompressors Creds ContentSubtype
        PreviousAttempts Authority]
      · iapply typedPointsto_combine _ _ _ Hchnn
        simp only [TypedPointsto.typedPointstoDef, named]
        rw [hcreds]
        iframe
      iapply HΦ
      iframe
      ileft
      isplitr
      · itrivial
      iexists fs', cms, tfs, afs,
        mkeys.flatMap (fun k => grpcHdr.mdKeyFields k ((Mo !! k).getD [])) ++
          rows.flatMap grpcHdr.rowFields
      iframe
      ipureintro
      rw [hm, List.take_length] at Hm
      refine ⟨?_, Hfs4.2, HM.1, HM.2.1, Hfs5.2, mkeys, Hfs6.1, rfl⟩
      rw [Hm.2.2, Hfs6.2]
      simp

end proof

end EtcdGrove
end Perennial
