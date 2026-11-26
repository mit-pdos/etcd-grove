/-
The proofs of `http.Header.Get` (`Net/Spec/net/http/Header__Get.lean`): `textproto.MIMEHeader(h).Get(key)`
(`MIMEHeader.Get.spec`) on the map of `hdrOwn h hb` (`Header.Get.wp_proof`) or `hdrRO h hb`
(`Header.Get.wp_proof_ro`), with `key`'s slice the one of `key`'s first line (`hdrGetL`), or none.
-/
module

public import Net.Spec.net.http.Header__Get
public import Net.Spec.net.textproto.MIMEHeader__Get

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section pure

/-- A name no line has is absent from a map whose names are the lines'. -/
theorem hdr_lookup_none (ms : GMap GoString GoSlice) (hb : List HdrLine) (key : GoString)
    (hdom : ∀ k, (ms !! k).isSome = decide (k ∈ hb.map Prod.fst))
    (hf : hb.find? (fun kv => decide (kv.1 = key)) = none) : ms !! key = none := by
  have hn : key ∉ hb.map Prod.fst := by
    intro hm
    obtain ⟨kv, hkv, hk⟩ := List.mem_map.1 hm
    have := List.find?_eq_none.1 hf kv hkv
    simp [hk] at this
  have := hdom key
  rw [decide_eq_false hn] at this
  cases h' : ms !! key with
  | none => rfl
  | some _ => rw [h'] at this; cases this

theorem hdrGetL_none (hb : List HdrLine) (key : GoString)
    (hf : hb.find? (fun kv => decide (kv.1 = key)) = none) : hdrGetL hb key = [] := by
  simp [hdrGetL, hf]

theorem hdrGetL_some (hb : List HdrLine) (key : GoString) (kv : HdrLine)
    (hf : hb.find? (fun kv => decide (kv.1 = key)) = some kv) : hdrGetL hb key = kv.2 := by
  simp [hdrGetL, hf]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem Header.Get.wp_proof
    (wp_Get : net.textproto.MIMEHeader.Get.spec (GF := GF) (hG := hG)) :
    Header.Get.spec (GF := GF) (hG := hG) := by
  intro h hb key Hk
  wp_start as Hown
  iunfold hdrOwn at Hown
  icases Hown with ⟨%ms, Hm, %Hdom, Hels⟩
  cases hf : hb.find? (fun kv => decide (kv.1 = key)) with
  | none =>
    have hnone := hdr_lookup_none ms hb key Hdom hf
    wp_auto
    wp_apply wp_Get h (DFrac.own 1) ms key (DFrac.own 1) [] $$ [Hm] as ⟨Hm, -⟩
    · unfold net.textproto.mimeVals
      rw [hnone]
      simp only []
      iframe
      ipureintro; first | exact ⟨Hk, rfl⟩ | exact Hk
    rw [hdrGetL_none hb key hf]
    simp only [List.head?_nil, Option.getD_none]
    iapply HΦ
    iunfold hdrOwn
    iexists ms
    iframe
    ipureintro; exact Hdom
  | some kv =>
    have hkv := List.mem_of_find?_eq_some hf
    have hk : kv.1 = key := by simpa using List.find?_some hf
    icases BigSepL.bigSepL_mem_acc (Φ := fun (kv : HdrLine) => iprop(∃ s : GoSlice,
        ⌜ms !! kv.1 = some s⌝ ∗ s ↦* ([kv.2] : List GoString))) hkv $$ Hels
      with ⟨⟨%s, %Hs, Hs⟩, Hels⟩
    have Hs' : ms !! key = some s := hk ▸ Hs
    wp_auto
    wp_apply wp_Get h (DFrac.own 1) ms key (DFrac.own 1) [kv.2] $$ [Hm Hs] as ⟨Hm, Hs⟩
    · unfold net.textproto.mimeVals
      rw [Hs']
      simp only []
      iframe
      ipureintro; exact Hk
    unfold net.textproto.mimeVals
    rw [Hs']
    simp only [List.head?_cons, Option.getD_some]
    rw [← hdrGetL_some hb key kv hf]
    iapply HΦ
    iunfold hdrOwn
    iexists ms
    iframe Hm
    isplitr
    · ipureintro; exact Hdom
    iapply Hels
    iexists s
    iframe Hs
    ipureintro; exact Hs

theorem Header.Get.wp_proof_ro
    (wp_Get : net.textproto.MIMEHeader.Get.spec (GF := GF) (hG := hG)) :
    Header.Get.spec_ro (GF := GF) (hG := hG) := by
  intro h hb key Hk
  wp_start as Hro
  iunfold hdrRO at Hro
  icases Hro with ⟨%ms, #Hm, %Hdom, #Hels⟩
  cases hf : hb.find? (fun kv => decide (kv.1 = key)) with
  | none =>
    have hnone := hdr_lookup_none ms hb key Hdom hf
    wp_auto
    wp_apply wp_Get h DFrac.discard ms key DFrac.discard [] $$ [] as -
    · unfold net.textproto.mimeVals
      rw [hnone]
      simp only []
      iframe #
      ipureintro; first | exact ⟨Hk, rfl⟩ | exact Hk
    rw [hdrGetL_none hb key hf]
    simp only [List.head?_nil, Option.getD_none]
    iapply HΦ
    itrivial
  | some kv =>
    have hkv := List.mem_of_find?_eq_some hf
    have hk : kv.1 = key := by simpa using List.find?_some hf
    ihave Hx := BigSepL.bigSepL_mem (Φ := fun (kv : HdrLine) => iprop(∃ s : GoSlice,
        ⌜ms !! kv.1 = some s⌝ ∗ s ↦*□ ([kv.2] : List GoString))) hkv $$ Hels
    icases Hx with ⟨%s, %Hs, #Hs⟩
    have Hs' : ms !! key = some s := hk ▸ Hs
    wp_auto
    wp_apply wp_Get h DFrac.discard ms key DFrac.discard [kv.2] $$ [] as -
    · unfold net.textproto.mimeVals
      rw [Hs']
      simp only []
      iframe #
      ipureintro; exact Hk
    simp only [List.head?_cons, Option.getD_some]
    rw [← hdrGetL_some hb key kv hf]
    iapply HΦ
    itrivial

end proof

end net.http
end Perennial
