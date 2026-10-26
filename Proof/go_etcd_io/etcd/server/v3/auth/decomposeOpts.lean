/-
`decomposeOpts`'s proof (the auth plan's E2g, 2026-10-25): `strings.Split` of the options on
`","` (Perennial's `strings.wp_Split`), the first field the token type, then a loop over the
others, each split on `"="` and put into the map, or the error `ErrInvalidAuthOpts` (the package's
fact `authInit`: a non-nil error).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.decomposeOpts
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.go_uber_org.zap.String
public import Perennial.Proof.strings.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.decomposeOpts.wp_proof (h_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG)) :
    auth.decomposeOpts.spec (GF := GF) (hG := hG) := by
  intro lg optstr
  wp_start as %Hlg
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HIO⟩
  iunfold authErrVar at HIO
  icases HIO with ⟨%eIO, #HeIO, -⟩
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply strings.wp_Split optstr go!"," (by decide) $$ [$Hstr] as %sl ⟨Hsl, -⟩
  ihave %Hslen := ownSlice_len $$ Hsl
  have Hne := _root_.Perennial.strings.split_ne_nil optstr go!","
  obtain ⟨f0, fs, Hfs⟩ : ∃ f0 fs, _root_.Perennial.strings.split optstr go!"," = f0 :: fs := by
    match h : _root_.Perennial.strings.split optstr go!",", Hne with
    | a :: r, _ => exact ⟨a, r, rfl⟩
  rw [Hfs] at Hslen
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
    simp only [List.length_cons] at Hslen; constructor <;> word
  simp only [Hb0, and_self, ↓reduceIte]
  rw [Hfs]
  wp_apply wp_load_slice_index sl (sint.Z (W64 0)) _ _ f0 (by decide) $$ [$Hsl] as Hsl
  · ipureintro; rfl
  (try wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %mp Hm
  (try wp_auto)
  ihave IH : iprop(∃ (n : w64) (mm : GMap GoString GoString), "i" ∷ i_ptr ↦ n ∗
      "Hm" ∷ mp ↦$ mm ∗ "%Hn" ∷ ⌜1 ≤ sint.Z n⌝) $$ [i Hm]
  · iexists W64 1, ∅
    iframe
    ipureintro; word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < (f0 :: fs).length := by word
    obtain ⟨f, Hfi⟩ : ∃ f, (f0 :: fs)[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨by word, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) _ _ f (by word) $$ [$Hsl] as Hsl
    · ipureintro; exact Hfi
    (try wp_auto)
    wp_apply strings.wp_Split f go!"=" (by decide) $$ [$Hstr] as %pl ⟨Hpl, -⟩
    ihave %Hplen := ownSlice_len $$ Hpl
    (try wp_auto)
    wp_if_destruct
    · obtain ⟨k, v, Hkv⟩ : ∃ k v, _root_.Perennial.strings.split f go!"=" = [k, v] := by
        have h2 : (_root_.Perennial.strings.split f go!"=").length = 2 := by
          rw [Hplen.1, Hif]; rfl
        match hx : _root_.Perennial.strings.split f go!"=", h2 with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      rw [Hkv]
      have Hb0' : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z pl.len := by
        rw [Hif]; constructor <;> decide
      have Hb1' : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z pl.len := by
        rw [Hif]; constructor <;> decide
      simp only [Hb0', Hb1', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index pl (sint.Z (W64 0)) _ _ k (by decide) $$ [$Hpl] as Hpl
      · ipureintro; rfl
      wp_apply (wp_map_lookup2 go.string go.string mp mm k) $$ [$Hm] as Hm
      (try wp_auto)
      wp_if_destruct
      · -- a key given twice: the error
        wp_if_destruct
        · exfalso; first | exact Hlg rfl | (apply Hlg; assumption)
        · wp_apply h_String _ _ as %f1 -
          (try wp_auto)
          simp only [Hb0', Hb1', _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index pl (sint.Z (W64 0)) _ _ k (by decide) $$ [$Hpl] as Hpl
          · ipureintro; rfl
          wp_apply h_String _ _ as %f2 -
          (try wp_auto)
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          (try wp_auto)
          wp_apply h_Error
          · ipureintro; exact Hlg
          (try wp_auto)
          wp_for_post
          iapply HΦ
          iright; ipureintro; exact ⟨by simp, by simp only [List.length_cons] at Hslen ⊢; word⟩
      · simp only [Hb0', Hb1', _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index pl (sint.Z (W64 1)) _ _ v (by decide) $$ [$Hpl] as Hpl
        · ipureintro; rfl
        (try wp_auto)
        simp only [Hb0', Hb1', _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index pl (sint.Z (W64 0)) _ _ k (by decide) $$ [$Hpl] as Hpl
        · ipureintro; rfl
        wp_apply (wp_mapInsert go.string mp mm k v) $$ [$Hm] as Hm
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, _
        iframe
        ipureintro; word
    · -- not one `key=value` pair: the error
      wp_if_destruct
      · exfalso; first | exact Hlg rfl | (apply Hlg; assumption)
      · wp_apply h_String _ _ as %f1 -
        (try wp_auto)
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply h_Error
        · ipureintro; exact Hlg
        (try wp_auto)
        wp_for_post
        iapply HΦ
        iright; ipureintro; exact ⟨by simp, by simp only [List.length_cons] at Hslen ⊢; word⟩
  · (try wp_auto)
    iapply HΦ
    ileft
    isplitl []
    · ipureintro; rfl
    isplitl []
    · ipureintro; rfl
    iexists mm; iexact Hm

end proof

end EtcdGrove
end Perennial
