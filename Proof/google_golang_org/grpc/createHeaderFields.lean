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
      · sorry
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
  sorry

end proof

end EtcdGrove
end Perennial
