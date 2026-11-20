/-
`Valid(data)` and `Unmarshal(data, ptr)` of the lab's `encoding/json` model: `jsonValid F`
(`Defs.lean`) by the registered scanner, then (`Unmarshal`) a syntax error or the kit's
`jsonUnmarshal`.
-/
module

public import Harness.Proof.encoding.json.Codec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

section spec
variable [JsonKit]
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [encoding.json.Assumptions] [JsonCodec GF]

set_option goose.wp.extras true

theorem wp_isSpace (c : w8) :
    {{ (True : IProp GF) }}
      (App (Val (@! encoding.json.isSpace)) (Val #c))
    {{ RET #(isSpaceB c); True }} := by
  wp_start
  wp_auto
  by_cases h1 : c = W8 32
  · have hb : isSpaceB c = true := by rw [h1]; rfl
    rw [hb]; simp only [h1, _root_.decide_true]
    wp_auto
    iapply HΦ; itrivial
  simp only [h1, _root_.decide_false]
  wp_auto
  by_cases h2 : c = W8 9
  · have hb : isSpaceB c = true := by rw [h2]; rfl
    rw [hb]; simp only [h2, _root_.decide_true]
    wp_auto
    iapply HΦ; itrivial
  simp only [h2, _root_.decide_false]
  wp_auto
  by_cases h3 : c = W8 10
  · have hb : isSpaceB c = true := by rw [h3]; rfl
    rw [hb]; simp only [h3, _root_.decide_true]
    wp_auto
    iapply HΦ; itrivial
  simp only [h3, _root_.decide_false]
  wp_auto
  have h1' : ¬ c = 32#8 := h1
  have h2' : ¬ c = 9#8 := h2
  have h3' : ¬ c = 10#8 := h3
  have hb : isSpaceB c = decide (c = W8 13) := by
    simp [isSpaceB, h1', h2', h3']
  rw [hb]
  iapply HΦ; itrivial

theorem wp_allSpace (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! encoding.json.allSpace)) (Val #b))
    {{ RET #(bs.all isSpaceB); b ↦*{dq} bs }} := by
  wp_start as Hs
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hs
  ihave IH : iprop(∃ (n : w64) (vv : w8),
      "i" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ vv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (bs.length : Int) ∧
        ∀ k < (sint.Z n).toNat, ∀ x, bs[k]? = some x → isSpaceB x = true⌝) $$ [i c]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    intro k hk; simp at hk
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < bs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, bs[(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z b.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index b (sint.Z n) bs dq x Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx
    wp_apply wp_isSpace x
    by_cases hsp : isSpaceB x = true
    · simp only [hsp]
      wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro k hk y hy
      by_cases hkn : k < (sint.Z n).toNat
      · exact Hn.2.2 k hkn y hy
      · have : k = (sint.Z n).toNat := by word
        subst this; rw [Hx] at hy; cases hy; exact hsp
    · simp only [Bool.not_eq_true] at hsp
      simp only [hsp]
      wp_auto
      wp_for_post
      have hall : bs.all isSpaceB = false := by
        rw [List.all_eq_false]
        exact ⟨x, List.mem_of_getElem? Hx, by simp [hsp]⟩
      rw [hall]
      iapply HΦ; iframe
  · have hall : bs.all isSpaceB = true := by
      rw [List.all_eq_true]
      intro y hy
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
      exact Hn.2.2 k (by word) _ (List.getElem?_eq_getElem hk)
    rw [hall]
    iapply HΦ; iframe

theorem jsonValid_iff (F : List w8 → Bool → w64 × w64) (bs : List w8)
    (hn : uint.nat (F bs true).2 ≤ bs.length) :
    jsonValid F bs ↔
      ((F bs true).1 = W64 0 ∧ (bs.drop (uint.nat (F bs true).2)).all isSpaceB = true) := by
  unfold jsonValid
  rw [List.all_eq_true]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1, hn, h3⟩

theorem wp_valid (F : List w8 → Bool → w64 × w64) (c : Loc) (data : GoSlice) (dq : DFrac)
    (bs : List w8) :
    {{ codecFns (GF := GF) c ∗ scanOk F scanFn ∗ data ↦*{dq} bs }}
      (App (App (Val (@! encoding.json.valid)) (Val #c)) (Val #data))
    {{ RET #(decide (jsonValid F bs)); data ↦*{dq} bs }} := by
  wp_start as ⟨#Hfns, #Hscan, Hs⟩
  unfold codecFns
  icases Hfns with ⟨-, -, #HS⟩
  unfold scanOk
  icases Hscan with ⟨%HF, #Hscan⟩
  wp_auto
  wp_apply Hscan $$ Hs
  iintro Hs
  wp_auto
  have hn := HF bs true
  ihave %Hlen := ownSlice_len $$ Hs
  have hnZ : sint.Z (F bs true).2 = uint.Z (F bs true).2 := by word
  have hnN : sint.nat (F bs true).2 = uint.nat (F bs true).2 := by
    show (sint.Z _).toNat = _; rw [hnZ]; rfl
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  have hsplit : 0 ≤ sint.Z (F bs true).2 ∧ sint.Z (F bs true).2 ≤ sint.Z data.len := by
    rw [hnZ]; constructor <;> word
  wp_if_destruct
  · rw [ite_eq_left ⟨hsplit.1, hsplit.2, Hwf.2⟩]
    ihave Hsplit := (ownSlice_split_all (F bs true).2 data dq bs hsplit).1 $$ Hs
    icases Hsplit with ⟨Hpre, Hrest⟩
    wp_auto
    wp_apply wp_allSpace $$ Hrest
    iintro Hrest
    wp_auto
    have hd : decide (jsonValid F bs) = (bs.drop (sint.nat (F bs true).2)).all isSpaceB := by
      rw [hnN, Bool.eq_iff_iff, decide_eq_true_iff, jsonValid_iff F bs hn]
      simp [Hif]
    rw [hd]
    iapply HΦ
    iapply (ownSlice_split_all (F bs true).2 data dq bs hsplit).2
    isplitl [Hpre]
    · iexact Hpre
    · iexact Hrest
  · have hd : decide (jsonValid F bs) = false := decide_eq_false (fun h => Hif h.1)
    rw [hd]
    iapply HΦ
    iexact Hs

/-- `Valid(data)`: whether `data` is one JSON value with whitespace around it (`jsonValid F`). -/
abbrev Valid.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (data : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ codecSet (GF := GF) ∗
      kitCodecOk F ∗ data ↦*{dq} bs }}
    (App (Val (@! encoding.json.Valid)) (Val #data))
  {{ RET #(decide (jsonValid F bs)); data ↦*{dq} bs }}

theorem Valid.wp_proof : Valid.spec (GF := GF) (hG := hG) := by
  intro F data dq bs
  wp_start as ⟨#Hset, #Hok, Hs⟩
  wp_auto
  wp_apply getCodec.wp_proof $$ [$Hset] as %c #Hfns
  unfold kitCodecOk
  icases Hok with ⟨-, -, #Hscan⟩
  wp_apply wp_valid F c data dq bs $$ [$Hfns $Hscan $Hs] as Hs
  iapply HΦ
  iexact Hs

/-- `Unmarshal(data, ptr)`: on valid JSON (`jsonValid F`), the kit's `jsonUnmarshal`
(`JsonCodec.dec`; `err` is nil exactly when it decoded); else a syntax error (non-nil), with
nothing decoded. -/
abbrev Unmarshal.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (data : GoSlice) (dq : DFrac) (bs : List w8)
    (ptr : GoInterface) (Ψ : Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ codecSet (GF := GF) ∗
      kitCodecOk F ∗ data ↦*{dq} bs ∗ JsonCodec.dec bs ptr Ψ }}
    (App (App (Val (@! encoding.json.Unmarshal)) (Val #data)) (Val #ptr))
  {{ (err : GoInterface), RET #err; data ↦*{dq} bs ∗
      ((⌜jsonValid F bs⌝ ∗ ∃ ok, ⌜err = interface.nil ↔ ok = true⌝ ∗ Ψ ok) ∨
       (⌜¬ jsonValid F bs ∧ err ≠ interface.nil⌝ ∗ JsonCodec.dec bs ptr Ψ)) }}

theorem Unmarshal.wp_proof : Unmarshal.spec (GF := GF) (hG := hG) := by
  intro F data dq bs ptr Ψ
  wp_start as ⟨#Hset, #Hok, Hs, Hdec⟩
  wp_auto
  wp_apply getCodec.wp_proof $$ [$Hset] as %c #Hfns
  unfold kitCodecOk
  icases Hok with ⟨-, #Hu, #Hscan⟩
  wp_apply wp_valid F c data dq bs $$ [$Hfns $Hscan $Hs] as Hs
  by_cases hv : jsonValid F bs
  · rw [decide_eq_true hv]
    wp_auto
    unfold codecFns
    icases Hfns with ⟨-, #Hum, -⟩
    wp_auto
    unfold unmarshalOk
    wp_apply Hu $$ %data %dq %bs %ptr %Ψ %_ %hv Hs Hdec
    iintro %err %ok Hs %Hok HΨ
    wp_auto
    iapply HΦ
    iframe Hs
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
    iright
    iframe Hdec
    ipureintro
    exact ⟨hv, by simp [interface.mkOk]⟩

end spec

end encoding.json

end Perennial
