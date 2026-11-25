/-
`vsrwire.Frame`'s generated decoder (`vsrwire`'s `json_model_gen.go`, jsongen's same-package
methods: `jdecRaw`, `jdecMember_Frame`, `jdec_Frame`) on a line's value `encEvent m`: it stores
`m`'s type and a fresh copy of the payload bytes. Over the specs of `jsoncodec`'s decoding helpers
(`Net/Spec/models_lab/jsoncodec/`), section hypotheses here, linked in `examples/vsrnet/Link.lean`.
Ported from dsverify-lab's `examples/vr/proof/VsrProof/Proof/vsrnetjson/Frame.lean` (lab master
915f964); `jdecRaw` copies the value itself (the lab's went through `RawMessage.UnmarshalJSON`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.Facts
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.LogDec
public import Net.Spec.models_lab.jsoncodec.At
public import Net.Spec.models_lab.jsoncodec.Empty
public import Net.Spec.models_lab.jsoncodec.Member
public import Net.Spec.models_lab.jsoncodec.Next
public import Net.Spec.models_lab.jsoncodec.Uint
public import Net.Spec.models_lab.jsoncodec.SkipSpace
public import Net.Spec.models_lab.jsoncodec.ValueEnd
public import Net.Spec.models_lab.jsoncodec.Valid
public import Net.Proof.models_lab.jsoncodec.DecBase

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false
set_option maxHeartbeats 2000000

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem vsrnet.takeWhile_ws (ws R : List w8) (c : w8) (hws : ∀ x ∈ ws, JsonScan.spB x = true)
    (hc : JsonScan.spB c = false) : (ws ++ c :: R).takeWhile JsonScan.spB = ws := by
  induction ws with
  | nil => simp [List.takeWhile_cons, hc]
  | cons x ws ih =>
    simp [List.takeWhile_cons, hws x (by simp), ih (fun y hy => hws y (by simp [hy]))]

theorem vsrnet.skipEnd_ws (bs ws R : List w8) (i : Nat) (c : w8)
    (hws : ∀ x ∈ ws, JsonScan.spB x = true) (hc : JsonScan.spB c = false)
    (h : bs.drop i = ws ++ c :: R) : JsonScan.skipEnd bs i = i + ws.length := by
  simp [JsonScan.skipEnd, h, vsrnet.takeWhile_ws ws R c hws hc]

theorem vsrnet.typeOf_eq (m : Msg) : pkg.events.typeOf m = W8 (VsrJson.typeN m : Int) := by
  cases m <;> rfl

theorem vsrnet.typeN_le (m : Msg) : VsrJson.typeN m ≤ 11 := by
  cases m <;> simp [VsrJson.typeN]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [vsrnet.Assumptions]
variable (wp_SkipSpace : models_lab.jsoncodec.SkipSpace.spec (GF := GF) (hG := hG))
variable (wp_ValueEnd : models_lab.jsoncodec.ValueEnd.spec (GF := GF) (hG := hG))
variable (wp_At : models_lab.jsoncodec.At.spec (GF := GF) (hG := hG))
variable (wp_Empty : models_lab.jsoncodec.Empty.spec (GF := GF) (hG := hG))
variable (wp_Member : models_lab.jsoncodec.Member.spec (GF := GF) (hG := hG))
variable (wp_Next : models_lab.jsoncodec.Next.spec (GF := GF) (hG := hG))
variable (wp_Uint : models_lab.jsoncodec.Uint.spec (GF := GF) (hG := hG))
variable (wp_Valid : models_lab.jsoncodec.Valid.spec (GF := GF) (hG := hG))

set_option goose.wp.extras true

include wp_SkipSpace wp_ValueEnd in
/-- `jdecRaw(b, i, p)` with `*p` nil, on a complete value `V` at `i` (not after whitespace):
`*p` becomes a fresh copy of `V`. -/
theorem vsrnet.wp_jdecRaw (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (mp : Loc)
    (V R : List w8) (c : w8) (hb : bs.drop (uint.nat i) = V ++ R) (hc : bs[uint.nat i]? = some c)
    (hs : JsonScan.spB c = false)
    (hsc : JsonScan.scanL (bs.drop (uint.nat i)) true = (0, V.length)) :
    {{ (b ↦*{dq} bs ∗ mp ↦ (slice.nil : GoSlice) : IProp GF) }}
      (App (App (App (Val (@! vsrwire.jdecRaw)) (Val #b)) (Val #i)) (Val #mp))
    {{ RET #(W64 ((uint.nat i + V.length : Nat) : Int)); b ↦*{dq} bs ∗
        ∃ m' : GoSlice, mp ↦ m' ∗ m' ↦* V ∗ ownSliceCap w8 m' (DFrac.own 1) }} := by
  wp_start as ⟨Hs, Hmp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  wp_auto
  wp_apply (models_lab.jsoncodec.wp_SkipSpace_ns wp_SkipSpace b dq bs i c hc hs) $$ Hs as Hs
  have hi : uint.nat i < bs.length := by
    rcases Nat.lt_or_ge (uint.nat i) bs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hc; cases hc
  have hle : uint.nat i + V.length ≤ bs.length := by
    have := congrArg List.length hb; simp at this; omega
  wp_apply (wp_ValueEnd b dq bs i (by omega) (by rw [hsc])) $$ Hs as Hs
  rw [hsc]
  simp only
  ihave %Hwf := ownSlice_wf $$ Hs
  ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hncap := ownSliceCap_nil (V := w8) (GF := GF)
  have hb2 : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (W64 ↑(uint.nat i + V.length)) ∧
      sint.Z (W64 ↑(uint.nat i + V.length)) ≤ sint.Z b.len := by word
  have hb1 : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (W64 ↑(uint.nat i + V.length)) ∧
      sint.Z (W64 ↑(uint.nat i + V.length)) ≤ sint.Z b.cap := by word
  rw [if_pos hb1]
  ihave ⟨-, Hm0, Hcap0⟩ := ownSlice_slice_with_cap (V := w8) (W64 0) (W64 0) slice.nil []
    ⟨by decide, by decide, by simp [slice.nil]⟩ $$ [Hnil Hncap]
  · isplitl []
    · iexact Hnil
    · iexact Hncap
  icases (ownSlice_slice i _ b dq bs hb2).1 $$ Hs with ⟨H1, H2, H3⟩
  have hsub : subslice (sint.nat i) (sint.nat (W64 ↑(uint.nat i + V.length))) bs = V := by
    rw [show sint.nat i = uint.nat i by word,
      show sint.nat (W64 ↑(uint.nat i + V.length)) = uint.nat i + V.length by word]
    simp only [subslice]; rw [List.drop_take, hb]; simp
  rw [hsub]
  wp_auto
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hm0 $Hcap0 $H2] as %m' ⟨Hm', Hcap', H2⟩
  rw [show subslice 0 0 ([] : List w8) = [] from rfl, List.nil_append]
  ihave Hs := (ownSlice_slice i _ b dq bs hb2).2 $$ [H1 H2 H3]
  · rw [hsub]; iframe
  iapply HΦ
  iframe

include wp_Uint in
/-- `jdecMember_Frame(b, i, "@type", p, e)` on the digits of `t` (≤ 255). -/
theorem vsrnet.wp_jdecMember_Frame_type (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (fr : vsrwire.Frame) (t : Nat) (c : w8) (rest : List w8)
    (hc : JsonScan.numEnd c) (hb : bs.drop (uint.nat i) = JsonScan.decN t ++ c :: rest)
    (ht : t ≤ 255) :
    {{ (b ↦*{dq} bs ∗ p ↦ fr : IProp GF) }}
      (App (App (App (App (App (Val (@! vsrwire.jdecMember_Frame)) (Val #b)) (Val #i))
        (Val #(go!"@type"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN t).length : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ vsrwire.Frame.mk (W8 (t : Int)) fr.Data' }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (wp_Uint b dq bs i _ t c rest hc hb (by simp; omega)) $$ Hs as Hs
  rw [show W8 (uint.Z (W64 (t : Int))) = W8 (t : Int) by word]
  iapply HΦ; iframe

include wp_SkipSpace wp_ValueEnd in
/-- `jdecMember_Frame(b, i, "data", p, e)` (`Data` nil) on a value `V` at `i`. -/
theorem vsrnet.wp_jdecMember_Frame_data (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (ty : w8) (V R : List w8) (c : w8) (hb : bs.drop (uint.nat i) = V ++ R)
    (hc : bs[uint.nat i]? = some c) (hs : JsonScan.spB c = false)
    (hsc : JsonScan.scanL (bs.drop (uint.nat i)) true = (0, V.length)) :
    {{ (b ↦*{dq} bs ∗ p ↦ vsrwire.Frame.mk ty slice.nil : IProp GF) }}
      (App (App (App (App (App (Val (@! vsrwire.jdecMember_Frame)) (Val #b)) (Val #i))
        (Val #(go!"data"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + V.length : Nat) : Int));
        b ↦*{dq} bs ∗ ∃ data : GoSlice, p ↦ vsrwire.Frame.mk ty data ∗ data ↦* V ∗
          ownSliceCap w8 data (DFrac.own 1) }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  wp_apply (vsrnet.wp_jdecRaw wp_SkipSpace wp_ValueEnd b dq bs i _ V R c hb hc hs hsc) $$ [Hs Data]
    as ⟨Hs, %m', Data, Hm, Hcap⟩
  · iframe
  ihave Hp : (p ↦ vsrwire.Frame.mk ty m' : IProp GF) $$ [Type' Data]
  · iapply typedPointsto_combine _ _ _ Hpnn
    simp only [typedPointstoDef]
    iframe
  iapply HΦ
  iframe

include wp_SkipSpace wp_ValueEnd wp_At wp_Empty wp_Member wp_Next wp_Uint in
/-- `jdec_Frame(b, i, p, e)` on an event's encoding after whitespace at `i` (`Data` nil). -/
theorem vsrnet.wp_jdec_Frame (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (ty : w8) (m : Msg) (ws rest : List w8) (hm : PlainMsg m)
    (hws : ∀ c ∈ ws, JsonScan.spB c = true)
    (hb0 : bs.drop (uint.nat i) = ws ++ (VsrJson.ser (VsrJson.evJV m) ++ rest)) :
    {{ (b ↦*{dq} bs ∗ p ↦ vsrwire.Frame.mk ty slice.nil : IProp GF) }}
      (App (App (App (App (Val (@! vsrwire.jdec_Frame)) (Val #b)) (Val #i)) (Val #p))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + ws.length + (VsrJson.ser (VsrJson.evJV m)).length : Nat) : Int));
        b ↦*{dq} bs ∗ ∃ data : GoSlice, p ↦ vsrwire.Frame.mk (pkg.events.typeOf m) data ∗
          data ↦* pkg.events.encPayload m ∗ ownSliceCap w8 data (DFrac.own 1) }} := by
  wp_start as ⟨Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hb := vsrnet.drop_app bs ws _ _ hb0
  have hwl : uint.nat i + ws.length ≤ bs.length := by
    have := congrArg List.length hb0; simp at this
    have := congrArg List.length hb; simp at this
    rcases Nat.lt_or_ge (uint.nat i + ws.length) bs.length with h | h
    · omega
    · rw [List.drop_eq_nil_of_le h] at hb; simp [VsrJson.ser_obj, VsrJson.evJV] at hb
  obtain ⟨j, hj⟩ : ∃ j : w64, uint.nat j = uint.nat i + ws.length :=
    ⟨W64 ((uint.nat i + ws.length : Nat) : Int), by word⟩
  rw [← hj] at hb
  have hser : VsrJson.ser (VsrJson.evJV m) =
      [123#8] ++ ((34#8 :: (go!"@type" ++ [34#8, 58#8])) ++ (JsonScan.decN (VsrJson.typeN m) ++
      ([44#8] ++ ((34#8 :: (go!"data" ++ [34#8, 58#8])) ++
        (VsrJson.ser (VsrJson.payJV m) ++ [125#8]))))) := by
    simp [VsrJson.ser, VsrJson.evJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT]
  rw [hser] at hb
  generalize hM0 : (34#8 :: (go!"@type" ++ [34#8, 58#8])) = M0 at hb
  generalize hV0 : JsonScan.decN (VsrJson.typeN m) = V0 at hb
  generalize hM1 : (34#8 :: (go!"data" ++ [34#8, 58#8])) = M1 at hb
  generalize hV1 : VsrJson.ser (VsrJson.payJV m) = V1 at hb
  simp only [List.append_assoc] at hb
  have hb1 := vsrnet.drop_app bs _ _ _ hb
  have hb2 := vsrnet.drop_app bs _ _ _ hb1
  have hb3 := vsrnet.drop_app bs _ _ _ hb2
  have hb4 := vsrnet.drop_app bs _ _ _ hb3
  have hb5 := vsrnet.drop_app bs _ _ _ hb4
  have hb6 := vsrnet.drop_app bs _ _ _ hb5
  have lM0 : M0.length = 8 := by rw [← hM0]; rfl
  have lM1 : M1.length = 7 := by rw [← hM1]; rfl
  have lser : (VsrJson.ser (VsrJson.evJV m)).length =
      1 + 8 + V0.length + 1 + 7 + V1.length + 1 := by
    rw [hser, ← hM0, ← hV0, ← hM1, ← hV1] at *; simp; omega
  simp only [List.length_cons, List.length_nil, lM0, lM1] at hb1 hb2 hb3 hb4 hb5 hb6
  have hlen := congrArg List.length hb6
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil] at hlen
  have hidx : ∀ k (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  have hc0 : bs[uint.nat j]? = some 123#8 := hidx _ _ _ (by rw [hb]; rfl)
  have hsk : JsonScan.skipEnd bs (uint.nat i) = uint.nat j := by
    rw [hj]; exact vsrnet.skipEnd_ws bs ws _ _ 123#8 hws (by decide)
      (by rw [hb0, hser]; simp only [List.append_assoc, List.singleton_append, List.cons_append]; rfl)
  wp_auto
  wp_apply (wp_At b dq bs i 123#8 (by omega) (by rw [hsk]; exact hc0)) $$ Hs as Hs
  rw [hsk, show W64 ((uint.nat j : Nat) : Int) = j by word]
  have hc1 : bs[uint.nat j + 1]? = some 34#8 := hidx _ _ _ (by rw [hb1, ← hM0]; rfl)
  wp_apply (wp_Empty b dq bs j 34#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
  ihave IH : iprop(∃ (n : Nat) (kw : w64) (tw : w8),
      "k" ∷ k_ptr ↦ kw ∗ "Hp" ∷ p ↦ vsrwire.Frame.mk tw slice.nil ∗
      "%Hn" ∷ ⌜(n = 0 ∧ uint.nat kw = uint.nat j + 1) ∨
        (n = 1 ∧ uint.nat kw = uint.nat j + 1 + 8 + V0.length + 1 ∧
          tw = W8 (VsrJson.typeN m : Int))⌝) $$ [k Hp]
  · iexists 0, _, ty; iframe; ipureintro; left; exact ⟨rfl, by word⟩
  wp_for IH
  try (rw [if_pos (by simp)]; wp_auto)
  rcases Hn with ⟨rfl, hk⟩ | ⟨rfl, hk, rfl⟩
  · have hm0 : bs.drop (uint.nat kw) = 34#8 :: (go!"@type" ++ 34#8 :: 58#8 :: (V0 ++ ([44#8] ++
        (M1 ++ (V1 ++ ([125#8] ++ rest)))))) := by
      rw [hk, hb1, ← hM0]; simp
    wp_apply (wp_Member b dq bs kw go!"@type" _ (by decide) hm0) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"@type").length + 3 : Nat) : Int)) =
        uint.nat j + 1 + 8 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"@type").length + 3 : Nat) : Int))) =
        JsonScan.decN (VsrJson.typeN m) ++ 44#8 :: (M1 ++ (V1 ++ ([125#8] ++ rest))) := by
      rw [hvz, hb2, ← hV0]; simp
    wp_apply (vsrnet.wp_jdecMember_Frame_type wp_Uint b dq bs _ p e _ (VsrJson.typeN m) 44#8 _
      JsonScan.numEnd_comma hv (by have := vsrnet.typeN_le m; omega)) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"@type").length + 3 : Nat) :
        Int)) + (JsonScan.decN (VsrJson.typeN m)).length : Nat) : Int)) =
        uint.nat j + 1 + 8 + V0.length := by
      rw [hvz, hV0]; word
    have hc : bs[uint.nat j + 1 + 8 + V0.length]? = some 44#8 := hidx _ _ _ (by rw [hb3]; rfl)
    wp_apply (wp_Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 1, _, _
    iframe
    ipureintro; right; exact ⟨rfl, by word, rfl⟩
  · have hm1 : bs.drop (uint.nat kw) = 34#8 :: (go!"data" ++ 34#8 :: 58#8 :: (V1 ++
        ([125#8] ++ rest))) := by
      rw [hk, hb4, ← hM1]; simp
    wp_apply (wp_Member b dq bs kw go!"data" _ (by decide) hm1) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"data").length + 3 : Nat) : Int)) =
        uint.nat j + 1 + 8 + V0.length + 1 + 7 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"data").length + 3 : Nat) : Int))) =
        V1 ++ ([125#8] ++ rest) := by rw [hvz, hb5]
    obtain ⟨ms, hms⟩ := VsrJson.payJV_obj m
    have hvc : bs[uint.nat (W64 ((uint.nat kw + (go!"data").length + 3 : Nat) : Int))]? =
        some 123#8 := hidx _ _ _ (by rw [hv, ← hV1, hms, VsrJson.ser_obj]; rfl)
    have hvsc : JsonScan.scanL (bs.drop (uint.nat (W64 ((uint.nat kw + (go!"data").length + 3 :
        Nat) : Int)))) true = (0, V1.length) := by
      rw [hv, ← hV1]
      have := VsrJson.top_v (VsrJson.payJV m) (VsrJson.payJV_ok m hm) ([125#8] ++ rest) 0 false
        true (VsrJson.payJV_maxd m) (by rw [hms]; trivial)
      simpa [JsonScan.scanL] using this
    wp_apply (vsrnet.wp_jdecMember_Frame_data wp_SkipSpace wp_ValueEnd b dq bs _ p e _ V1 _ 123#8
      hv hvc (by decide) hvsc) $$ [Hs Hp] as ⟨Hs, %data, Hp, Hd, Hcap⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"data").length + 3 : Nat) :
        Int)) + V1.length : Nat) : Int)) = uint.nat j + 1 + 8 + V0.length + 1 + 7 + V1.length := by
      rw [hvz]; word
    have hc : bs[uint.nat j + 1 + 8 + V0.length + 1 + 7 + V1.length]? = some 125#8 :=
      hidx _ _ _ (by rw [hb6]; rfl)
    wp_apply (wp_Next b dq bs _ 125#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    rw [lser, vsrnet.typeOf_eq]
    rw [show W64 ((uint.nat j + 1 + 8 + V0.length + 1 + 7 + V1.length + 1 : Nat) : Int)
      = W64 ((uint.nat i + ws.length + (1 + 8 + V0.length + 1 + 7 + V1.length + 1) : Nat) : Int)
      by congr 2; omega]
    rw [show pkg.events.encPayload m = V1 by rw [← hV1]; rfl]
    iapply HΦ
    iframe

include wp_SkipSpace wp_ValueEnd wp_At wp_Empty wp_Member wp_Next wp_Uint wp_Valid in
/-- **`TypeCodecs.frame`, proved**: `(*vsrwire.Frame).JSONModelUnmarshal` meets the kit's contract
(`decP`'s frame case: whitespace and a line's value `encEvent m` into a `Frame` with nil `Data`;
the other cases are at other pointer types). -/
theorem vsrnet.frameUnmarshalOk (l : Loc) :
    ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
      #(methods (go.GoType.PointerType vsrwire.Frame.ty) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType vsrwire.Frame.ty) #l) := by
  unfold encoding.json.unmarshalAt
  iintro %data %dq %bs %Ψ %Φ Hd Hdec HΦ
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  icases Hdec with (⟨%_, %ws, %m, %p, %fr, %hb, %hws, %hm, %hfr, %hptr, Hp, Hk⟩ |
    ⟨%_, %_, %_, %m, %p, %hb, %hm, %hmb, %hptr, -⟩ | ⟨%_, %es, %p, %hb, %hes, %hptr, -⟩)
  rotate_left
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    revert hty
    cases m <;> simp only [pkg.events.payloadTy, vsrwire.Frame.ty, pkg.events.Request.ty,
      pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty,
      pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty,
      pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty,
      go.GoType.Named.injEq, go.GoType.PointerType.injEq, reduceCtorEq] <;>
      exact fun h => absurd h.1 (by decide)
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [vsrwire.Frame.ty, go.GoType.PointerType.injEq, reduceCtorEq] at hty
  rotate_left
  have hlp := ((interface_mkOk_inj _ _ _ _).1 hptr).2
  rw [hlp]
  obtain ⟨ty, d⟩ := fr
  simp only at hfr
  subst hfr
  subst hb
  ihave %Hlen := ownSlice_len $$ Hd
  have hsp : ∀ c ∈ ws, JsonScan.spB c = true := fun c hc => by
    rw [← vsrnet.isSpaceB_spB]; exact hws c hc
  have hlen : (ws ++ VsrWire.encEvent m).length < 2 ^ 64 := by
    have := models_lab.jsoncodec.len_lt data _ Hlen; omega
  have hval := vsrnet.encEvent_valid ws m hws hm hlen
  have hsc : JsonScan.scanL (ws ++ VsrWire.encEvent m) true =
      (0, (ws ++ VsrWire.encEvent m).length) := by
    have := VsrJson.scanL_line ws m [] true hsp hm
    simp only [List.append_nil] at this
    simp only [VsrWire.encEvent, this, List.length_append]
  wp_method_call
  wp_auto
  wp_apply (wp_Valid data dq _ hsc) $$ Hd as Hd
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hp
  rw [decide_eq_false Hpnn]
  wp_auto
  have hb0 : (ws ++ VsrWire.encEvent m).drop (uint.nat (W64 0)) =
      ws ++ (VsrJson.ser (VsrJson.evJV m) ++ []) := by
    simp [VsrWire.encEvent, VsrJson.encEvent_plain m hm]
  wp_apply (vsrnet.wp_jdec_Frame wp_SkipSpace wp_ValueEnd wp_At wp_Empty wp_Member wp_Next wp_Uint
    data dq _ (W64 0) p err_ptr ty m ws [] hm hsp hb0) $$ [Hd Hp] as ⟨Hd, %d', Hp, Hpay, Hcap⟩
  · iframe
  iapply HΦ $$ Hd
  ileft
  isplitr
  · ipureintro; exact hval
  iexists true
  isplitr
  · ipureintro; simp
  iapply Hk
  iframe

end proof

end Perennial.github_com.tangledbytes.go_vsr.examples
