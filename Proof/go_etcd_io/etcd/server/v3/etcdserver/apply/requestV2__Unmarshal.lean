/-
Proof of `(*requestV2).Unmarshal` (`legacy_request.go:44`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.requestV2__Unmarshal
public import Spec.google_golang_org.protobuf.encoding.protowire.ConsumeTag
public import Spec.google_golang_org.protobuf.encoding.protowire.ConsumeVarint
public import Spec.google_golang_org.protobuf.encoding.protowire.ConsumeBytes
public import Spec.google_golang_org.protobuf.encoding.protowire.ConsumeFieldValue
public import Spec.google_golang_org.protobuf.encoding.protowire.ParseError
public import Spec.fmt.ErrorfNamed

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply
  go_etcd_io.etcd.server.v3.etcdserver.apply.requestV2
  google_golang_org.protobuf.encoding

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- Advancing a byte subslice `s ↦*{dq} rem` by `n` bytes while preserving the closing wand
back to `data ↦*{dq} bs`. -/
private theorem slice_advance (s data : GoSlice) (rem bs : List w8) (dq : DFrac) (n : w64)
    (h0 : 0 ≤ sint.Z n) (hn : sint.nat n ≤ rem.length) :
    iprop(s ↦*{dq} rem ∗ (s ↦*{dq} rem -∗ data ↦*{dq} bs) : IProp GF) ⊢
      ⌜(0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z s.len) ∧ sint.Z s.len ≤ sint.Z s.cap⌝ ∗
      slice.slice s w8 n s.len ↦*{dq} rem.drop (sint.nat n) ∗
      (slice.slice s w8 n s.len ↦*{dq} rem.drop (sint.nat n) -∗ data ↦*{dq} bs) := by
  iintro ⟨Hs, Hback⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z s.len := ⟨h0, by obtain ⟨_, _⟩ := Hlen; word⟩
  icases (ownSlice_split_all n s dq rem Hbnd).1 $$ Hs with ⟨Hs1, Hs2⟩
  isplitr
  · ipureintro; exact ⟨Hbnd, Hwf.2⟩
  iframe Hs2
  iintro Hs2
  iapply Hback
  iapply (ownSlice_split_all n s dq rem Hbnd).2
  iframe Hs1 Hs2

private theorem slice_advance_sub (s data : GoSlice) (rem bs : List w8) (dq : DFrac) (n m : w64)
    (h0 : 0 ≤ sint.Z m) (hm : sint.nat m ≤ rem.length) :
    iprop(slice.slice s w8 n s.len ↦*{dq} rem ∗
        (slice.slice s w8 n s.len ↦*{dq} rem -∗ data ↦*{dq} bs) : IProp GF) ⊢
      ⌜(0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z (s.len - n)) ∧ sint.Z (s.len - n) ≤ sint.Z (s.cap - n)⌝ ∗
      slice.slice (slice.slice s w8 n s.len) w8 m (s.len - n) ↦*{dq} rem.drop (sint.nat m) ∗
      (slice.slice (slice.slice s w8 n s.len) w8 m (s.len - n) ↦*{dq} rem.drop (sint.nat m) -∗
        data ↦*{dq} bs) :=
  slice_advance (slice.slice s w8 n s.len) data rem bs dq m h0 hm

private theorem errorfArgOk_type (typ : protowire.Type') :
    fmt.ErrorfArgOk (interface.mkOk protowire.Type'.ty #typ) := by
  right
  refine ⟨⟨go!"google.golang.org/protobuf/encoding/protowire.Type", ?_, ?_⟩, ?_⟩
  · simp [protowire.Type'.ty]
  · simp [fmt.errorfNamedTypes]
  · show _root_.Perennial.fmt.IsBasicType (underlying protowire.Type'.ty)
    rw [show underlying protowire.Type'.ty = go.int8 from go.IsUnderlying.is_underlying]
    simp [_root_.Perennial.fmt.IsBasicType, _root_.Perennial.fmt.IsIntType]

private theorem errorfArgOk_number (num : protowire.Number) :
    fmt.ErrorfArgOk (interface.mkOk protowire.Number.ty #num) := by
  right
  refine ⟨⟨go!"google.golang.org/protobuf/encoding/protowire.Number", ?_, ?_⟩, ?_⟩
  · simp [protowire.Number.ty]
  · simp [fmt.errorfNamedTypes]
  · show _root_.Perennial.fmt.IsBasicType (underlying protowire.Number.ty)
    rw [show underlying protowire.Number.ty = go.int32 from go.IsUnderlying.is_underlying]
    simp [_root_.Perennial.fmt.IsBasicType, _root_.Perennial.fmt.IsIntType]

private theorem v2UnmarshalLoop_cons_tag_none (b : w8) (rem : List w8) (acc : requestV2)
    (h : protowire.consumeTag (b :: rem) = none) :
    apply.v2UnmarshalLoop (b :: rem) acc = none := by
  rw [apply.v2UnmarshalLoop.eq_def]
  simp [h]

private theorem v2UnmarshalLoop_cons_tag_some (b : w8) (rem : List w8) (acc : requestV2)
    (num : w32) (typ : w8) (n : Nat)
    (htag : protowire.consumeTag (b :: rem) = some (num, typ, n))
    (h1 : 1 ≤ n) :
    apply.v2UnmarshalLoop (b :: rem) acc =
      if num = W32 1 then
        if typ ≠ W8 0 then none
        else
          match protowire.consumeVarint ((b :: rem).drop n) with
          | none => none
          | some (v, m) =>
            apply.v2UnmarshalLoop (((b :: rem).drop n).drop m) { acc with ID' := v }
      else if num = W32 4 ∨ num = W32 3 ∨ num = W32 2 then
        if typ ≠ W8 2 then none
        else
          match protowire.consumeBytes ((b :: rem).drop n) with
          | none => none
          | some (v, m) =>
            let acc' :=
              if num = W32 2 then { acc with Method' := v }
              else if num = W32 3 then { acc with Path' := v }
              else if num = W32 4 then { acc with Val' := v }
              else acc
            apply.v2UnmarshalLoop (((b :: rem).drop n).drop m) acc'
      else
        match protowire.consumeFieldValue num typ ((b :: rem).drop n) with
        | none => none
        | some m =>
          apply.v2UnmarshalLoop (((b :: rem).drop n).drop m) acc := by
  rw [apply.v2UnmarshalLoop.eq_def]
  simp only [htag, h1, reduceCtorEq, ↓reduceDIte]
  rfl

theorem apply.requestV2.Unmarshal.wp_proof
    (hTag : protowire.ConsumeTag.spec (GF := GF) (hG := hG))
    (hVarint : protowire.ConsumeVarint.spec (GF := GF) (hG := hG))
    (hBytes : protowire.ConsumeBytes.spec (GF := GF) (hG := hG))
    (hFieldVal : protowire.ConsumeFieldValue.spec (GF := GF) (hG := hG))
    (hPE : protowire.ParseError.spec (GF := GF) (hG := hG))
    (hErr : fmt.ErrorfNamed.spec (GF := GF) (hG := hG)) :
    apply.requestV2.Unmarshal.spec (GF := GF) (hG := hG) := by
  intro r_in r0 data bs dq
  wp_start as ⟨Hr, Hdata⟩
  ihave #Ppw : isPkgInit (PROP := IProp GF)
      pkg_id.google_golang_org.protobuf.encoding.protowire $$ []
  · iPkgInit
  ihave #Pfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  ihave IH : (∃ (s : GoSlice) (rem : List w8) (acc : requestV2),
      "r" ∷ r_ptr ↦ r_in ∗
      "data" ∷ data_ptr ↦ s ∗
      "Hs" ∷ s ↦*{dq} rem ∗
      "Hback" ∷ (s ↦*{dq} rem -∗ data ↦*{dq} bs) ∗
      "Hr" ∷ r_in ↦ acc ∗
      "%Hloop" ∷ ⌜apply.v2UnmarshalLoop rem acc = apply.v2Decode bs⌝ : IProp GF)
    $$ [r data Hdata Hr]
  · iexists data, bs, zeroValDef
    iframe r data Hdata Hr
    isplitl
    · iintro H; iexact H
    ipureintro; rfl
  wp_for IH
  ihave %Hslen := ownSlice_len _ _ _ $$ Hs
  wp_if_destruct
  · -- `len(data) > 0`
    have Hrem_pos : 0 < rem.length := by obtain ⟨_, _⟩ := Hslen; word
    rcases rem with _ | ⟨b0, rem_tl⟩
    · simp at Hrem_pos
    · wp_apply (hTag s (b0 :: rem_tl) dq) $$ [$Ppw $Hs] as %num %typ %n ⟨Hs, %Htag⟩
      wp_if_destruct
      · -- `n < 0` on `ConsumeTag`
        rcases Htag with ⟨_, Htnone⟩ | ⟨h0, _, _, _⟩
        · wp_apply (hPE n Hif) $$ [$Ppw] as %err %Herr
          wp_for_post
          iapply HΦ
          ihave Hdata := Hback $$ Hs
          iframe Hdata
          have Hdec : apply.v2Decode bs = none := by
            rw [← Hloop, v2UnmarshalLoop_cons_tag_none b0 rem_tl acc Htnone]
          simp only [Hdec]
          isplitr
          · ipureintro; exact Herr
          iexists acc; iframe Hr
        · word
      · -- `n >= 0` on `ConsumeTag`
        rcases Htag with ⟨hneg, _⟩ | ⟨h0, h1, hnlen, Htsome⟩
        · word
        icases slice_advance s data (b0 :: rem_tl) bs dq n h0 hnlen $$ [$Hs $Hback]
          with ⟨%Hbnd, Hs, Hback⟩
        simp only [Hbnd.1, Hbnd.2, _root_.and_self]
        wp_auto
        have Hstep := v2UnmarshalLoop_cons_tag_some b0 rem_tl acc num typ (sint.nat n) Htsome h1
        wp_if_destruct
        · -- `number == 1` (`num` is substituted with `W32 1`)
          wp_if_destruct
          · -- `typ == VarintType` (`typ` is substituted with `W8 0`)
            wp_apply (hVarint (slice.slice s w8 n s.len) ((b0 :: rem_tl).drop (sint.nat n)) dq)
              $$ [$Ppw $Hs] as %val %m ⟨Hs, %Hvar⟩
            wp_if_destruct
            · -- `m < 0` on `ConsumeVarint`
              rcases Hvar with ⟨_, Hvnone⟩ | ⟨hm0, _, _⟩
              · wp_apply (hPE m Hif) $$ [$Ppw] as %err %Herr
                wp_for_post
                iapply HΦ
                ihave Hdata := Hback $$ Hs
                iframe Hdata
                have Hdec : apply.v2Decode bs = none := by
                  rw [← Hloop, Hstep]
                  simp only [Hvnone, ne_eq, not_true_eq_false, ↓reduceIte]
                simp only [Hdec]
                isplitr
                · ipureintro; exact Herr
                iexists acc; iframe Hr
              · word
            · -- `m >= 0` on `ConsumeVarint`
              rcases Hvar with ⟨hmneg, _⟩ | ⟨hm0, hmlen, Hvsome⟩
              · word
              icases slice_advance_sub s data
                ((b0 :: rem_tl).drop (sint.nat n)) bs dq n m hm0 hmlen
                $$ [$Hs $Hback] with ⟨%Hmbnd, Hs, Hback⟩
              simp only [Hmbnd.1.1, Hmbnd.1.2, Hmbnd.2, _root_.and_self, ↓reduceIte]
              wp_auto
              wp_for_post
              iframe HΦ
              iexists (slice.slice (slice.slice s w8 n s.len) w8 m (s.len - n)),
                (((b0 :: rem_tl).drop (sint.nat n)).drop (sint.nat m)), { acc with ID' := val }
              iframe r data Hs Hback Hr
              ipureintro
              rw [← Hloop, Hstep]
              simp only [Hvsome, ne_eq, not_true_eq_false, ↓reduceIte]
          · -- `typ != VarintType` (`Hif : ¬ typ = W8 0`)
            have Htyp : typ ≠ W8 0 := Hif
            wp_apply (wp_slice_literal (l := [interface.mkOk protowire.Type'.ty #typ]))
            isplitr
            · ipureintro; rfl
            iintro %asl ⟨Hasl, -⟩
            wp_auto
            wp_apply (hErr _ _ [interface.mkOk protowire.Type'.ty #typ] (DFrac.own 1))
              $$ [$Pfmt $Hasl] as %err _
            · ipureintro
              intro a ha
              simp only [List.mem_singleton] at ha
              subst ha
              exact errorfArgOk_type typ
            wp_for_post
            iapply HΦ
            ihave Hdata := Hback $$ Hs
            iframe Hdata
            have Hdec : apply.v2Decode bs = none := by
              rw [← Hloop, Hstep]
              simp only [ne_eq, Htyp, not_false_eq_true, ↓reduceIte]
            simp only [Hdec]
            isplitr
            · ipureintro; simp
            iexists acc; iframe Hr
        · -- `number != 1` (`Hif : ¬ num = W32 1`)
          have Hnum1 : num ≠ W32 1 := Hif
          wp_if_destruct
          · -- `number == 4` (`num` is substituted with `W32 4`)
            wp_if_destruct
            · -- `typ == BytesType` (`typ` is substituted with `W8 2`)
              wp_apply (hBytes (slice.slice s w8 n s.len) ((b0 :: rem_tl).drop (sint.nat n)) dq)
                $$ [$Ppw $Hs] as %vsl %m Hbres
              icases Hbres with (⟨⟨%Hmneg, %Hbnone⟩, Hs⟩ | ⟨%v, %Hbok, Hvsl, Hvback⟩)
              · wp_if_destruct
                · wp_apply (hPE m Hif) $$ [$Ppw] as %err %Herr
                  wp_for_post
                  iapply HΦ
                  ihave Hdata := Hback $$ Hs
                  iframe Hdata
                  have Hdec : apply.v2Decode bs = none := by
                    rw [← Hloop, Hstep]
                    simp only [Hbnone, Hnum1, ne_eq, not_true_eq_false, _root_.true_or, ↓reduceIte]
                  simp only [Hdec]
                  isplitr
                  · ipureintro; exact Herr
                  iexists acc; iframe Hr
                · word
              · obtain ⟨hm0, hmlen, Hbsome⟩ := Hbok
                wp_if_destruct
                · word
                wp_apply (wp_bytes_to_string vsl v dq) $$ Hvsl as Hvsl
                ihave Hs := Hvback $$ Hvsl
                icases slice_advance_sub s data
                  ((b0 :: rem_tl).drop (sint.nat n)) bs dq n m hm0 hmlen
                  $$ [$Hs $Hback] with ⟨%Hmbnd, Hs, Hback⟩
                simp only [Hmbnd.1.1, Hmbnd.1.2, Hmbnd.2, _root_.and_self, ↓reduceIte]
                wp_auto
                wp_for_post
                iframe HΦ
                iexists (slice.slice (slice.slice s w8 n s.len) w8 m (s.len - n)),
                  (((b0 :: rem_tl).drop (sint.nat n)).drop (sint.nat m)), { acc with Val' := v }
                iframe r data Hs Hback Hr
                ipureintro
                rw [← Hloop, Hstep]
                have h42 : (W32 4 = W32 2) = False := by decide
                have h43 : (W32 4 = W32 3) = False := by decide
                simp only [Hbsome, Hnum1, h42, h43, ne_eq, not_true_eq_false, _root_.true_or, ↓reduceIte]
            · -- `typ != BytesType` (`Hif : ¬ typ = W8 2`)
              have Htyp : typ ≠ W8 2 := Hif
              wp_apply (wp_slice_literal (l := [interface.mkOk protowire.Number.ty #(W32 4),
                interface.mkOk protowire.Type'.ty #typ]))
              isplitr
              · ipureintro; rfl
              iintro %asl ⟨Hasl, -⟩
              wp_auto
              wp_apply (hErr _ _ [interface.mkOk protowire.Number.ty #(W32 4),
                interface.mkOk protowire.Type'.ty #typ] (DFrac.own 1))
                $$ [$Pfmt $Hasl] as %err _
              · ipureintro
                intro a ha
                simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
                rcases ha with rfl | rfl
                · exact errorfArgOk_number (W32 4)
                · exact errorfArgOk_type typ
              wp_for_post
              iapply HΦ
              ihave Hdata := Hback $$ Hs
              iframe Hdata
              have Hdec : apply.v2Decode bs = none := by
                rw [← Hloop, Hstep]
                simp only [Hnum1, ne_eq, Htyp, not_false_eq_true, _root_.true_or, ↓reduceIte]
              simp only [Hdec]
              isplitr
              · ipureintro; simp
              iexists acc; iframe Hr
          · -- `number != 4`
            have Hnum4 : num ≠ W32 4 := Hif
            wp_if_destruct
            · -- `number == 3` (`num` is substituted with `W32 3`)
              wp_if_destruct
              · -- `typ == BytesType` (`typ` is substituted with `W8 2`)
                wp_apply (hBytes (slice.slice s w8 n s.len) ((b0 :: rem_tl).drop (sint.nat n)) dq)
                  $$ [$Ppw $Hs] as %vsl %m Hbres
                icases Hbres with (⟨⟨%Hmneg, %Hbnone⟩, Hs⟩ | ⟨%v, %Hbok, Hvsl, Hvback⟩)
                · wp_if_destruct
                  · wp_apply (hPE m Hif) $$ [$Ppw] as %err %Herr
                    wp_for_post
                    iapply HΦ
                    ihave Hdata := Hback $$ Hs
                    iframe Hdata
                    have Hdec : apply.v2Decode bs = none := by
                      rw [← Hloop, Hstep]
                      simp only [Hbnone, Hnum1, ne_eq, not_true_eq_false, _root_.true_or, _root_.or_true, ↓reduceIte]
                    simp only [Hdec]
                    isplitr
                    · ipureintro; exact Herr
                    iexists acc; iframe Hr
                  · word
                · obtain ⟨hm0, hmlen, Hbsome⟩ := Hbok
                  wp_if_destruct
                  · word
                  wp_apply (wp_bytes_to_string vsl v dq) $$ Hvsl as Hvsl
                  ihave Hs := Hvback $$ Hvsl
                  icases slice_advance_sub s data
                    ((b0 :: rem_tl).drop (sint.nat n)) bs dq n m hm0 hmlen
                    $$ [$Hs $Hback] with ⟨%Hmbnd, Hs, Hback⟩
                  simp only [Hmbnd.1.1, Hmbnd.1.2, Hmbnd.2, _root_.and_self, ↓reduceIte]
                  wp_auto
                  wp_for_post
                  iframe HΦ
                  iexists (slice.slice (slice.slice s w8 n s.len) w8 m (s.len - n)),
                    (((b0 :: rem_tl).drop (sint.nat n)).drop (sint.nat m)), { acc with Path' := v }
                  iframe r data Hs Hback Hr
                  ipureintro
                  rw [← Hloop, Hstep]
                  have h32 : (W32 3 = W32 2) = False := by decide
                  simp only [Hbsome, Hnum1, h32, ne_eq, not_true_eq_false, _root_.true_or, _root_.or_true, ↓reduceIte]
              · -- `typ != BytesType` (`Hif : ¬ typ = W8 2`)
                have Htyp : typ ≠ W8 2 := Hif
                wp_apply (wp_slice_literal (l := [interface.mkOk protowire.Number.ty #(W32 3),
                  interface.mkOk protowire.Type'.ty #typ]))
                isplitr
                · ipureintro; rfl
                iintro %asl ⟨Hasl, -⟩
                wp_auto
                wp_apply (hErr _ _ [interface.mkOk protowire.Number.ty #(W32 3),
                  interface.mkOk protowire.Type'.ty #typ] (DFrac.own 1))
                  $$ [$Pfmt $Hasl] as %err _
                · ipureintro
                  intro a ha
                  simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
                  rcases ha with rfl | rfl
                  · exact errorfArgOk_number (W32 3)
                  · exact errorfArgOk_type typ
                wp_for_post
                iapply HΦ
                ihave Hdata := Hback $$ Hs
                iframe Hdata
                have Hdec : apply.v2Decode bs = none := by
                  rw [← Hloop, Hstep]
                  simp only [Hnum1, ne_eq, Htyp, not_false_eq_true, _root_.true_or, _root_.or_true, ↓reduceIte]
                simp only [Hdec]
                isplitr
                · ipureintro; simp
                iexists acc; iframe Hr
            · -- `number != 3`
              have Hnum3 : num ≠ W32 3 := Hif
              wp_if_destruct
              · -- `number == 2` (`num` is substituted with `W32 2`)
                wp_if_destruct
                · -- `typ == BytesType` (`typ` is substituted with `W8 2`)
                  wp_apply (hBytes (slice.slice s w8 n s.len) ((b0 :: rem_tl).drop (sint.nat n)) dq)
                    $$ [$Ppw $Hs] as %vsl %m Hbres
                  icases Hbres with (⟨⟨%Hmneg, %Hbnone⟩, Hs⟩ | ⟨%v, %Hbok, Hvsl, Hvback⟩)
                  · wp_if_destruct
                    · wp_apply (hPE m Hif) $$ [$Ppw] as %err %Herr
                      wp_for_post
                      iapply HΦ
                      ihave Hdata := Hback $$ Hs
                      iframe Hdata
                      have Hdec : apply.v2Decode bs = none := by
                        rw [← Hloop, Hstep]
                        simp only [Hbnone, Hnum1, ne_eq, not_true_eq_false, _root_.or_true, ↓reduceIte]
                      simp only [Hdec]
                      isplitr
                      · ipureintro; exact Herr
                      iexists acc; iframe Hr
                    · word
                  · obtain ⟨hm0, hmlen, Hbsome⟩ := Hbok
                    wp_if_destruct
                    · word
                    wp_apply (wp_bytes_to_string vsl v dq) $$ Hvsl as Hvsl
                    ihave Hs := Hvback $$ Hvsl
                    icases slice_advance_sub s data
                      ((b0 :: rem_tl).drop (sint.nat n)) bs dq n m hm0 hmlen
                      $$ [$Hs $Hback] with ⟨%Hmbnd, Hs, Hback⟩
                    simp only [Hmbnd.1.1, Hmbnd.1.2, Hmbnd.2, _root_.and_self, ↓reduceIte]
                    wp_auto
                    wp_for_post
                    iframe HΦ
                    iexists (slice.slice (slice.slice s w8 n s.len) w8 m (s.len - n)),
                      (((b0 :: rem_tl).drop (sint.nat n)).drop (sint.nat m)), { acc with Method' := v }
                    iframe r data Hs Hback Hr
                    ipureintro
                    rw [← Hloop, Hstep]
                    simp only [Hbsome, Hnum1, ne_eq, not_true_eq_false, _root_.or_true, ↓reduceIte]
                · -- `typ != BytesType` (`Hif : ¬ typ = W8 2`)
                  have Htyp : typ ≠ W8 2 := Hif
                  wp_apply (wp_slice_literal (l := [interface.mkOk protowire.Number.ty #(W32 2),
                    interface.mkOk protowire.Type'.ty #typ]))
                  isplitr
                  · ipureintro; rfl
                  iintro %asl ⟨Hasl, -⟩
                  wp_auto
                  wp_apply (hErr _ _ [interface.mkOk protowire.Number.ty #(W32 2),
                    interface.mkOk protowire.Type'.ty #typ] (DFrac.own 1))
                    $$ [$Pfmt $Hasl] as %err _
                  · ipureintro
                    intro a ha
                    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
                    rcases ha with rfl | rfl
                    · exact errorfArgOk_number (W32 2)
                    · exact errorfArgOk_type typ
                  wp_for_post
                  iapply HΦ
                  ihave Hdata := Hback $$ Hs
                  iframe Hdata
                  have Hdec : apply.v2Decode bs = none := by
                    rw [← Hloop, Hstep]
                    simp only [Hnum1, ne_eq, Htyp, not_false_eq_true, _root_.or_true, ↓reduceIte]
                  simp only [Hdec]
                  isplitr
                  · ipureintro; simp
                  iexists acc; iframe Hr
              · -- `default`: `number` not in `{1, 2, 3, 4}`
                have Hnum2 : num ≠ W32 2 := Hif
                wp_apply (hFieldVal num typ (slice.slice s w8 n s.len)
                  ((b0 :: rem_tl).drop (sint.nat n)) dq) $$ [$Ppw $Hs]
                  as %m ⟨Hs, %Hfval⟩
                wp_if_destruct
                · -- `m < 0` on `ConsumeFieldValue`
                  rcases Hfval with ⟨_, Hfnone⟩ | ⟨hm0, _, _⟩
                  · wp_apply (hPE m Hif) $$ [$Ppw] as %err %Herr
                    wp_for_post
                    iapply HΦ
                    ihave Hdata := Hback $$ Hs
                    iframe Hdata
                    have Hdec : apply.v2Decode bs = none := by
                      rw [← Hloop, Hstep]
                      simp only [Hnum1, Hnum4, Hnum3, Hnum2, Hfnone, _root_.or_self, ↓reduceIte]
                    simp only [Hdec]
                    isplitr
                    · ipureintro; exact Herr
                    iexists acc; iframe Hr
                  · word
                · -- `m >= 0` on `ConsumeFieldValue`
                  rcases Hfval with ⟨hmneg, _⟩ | ⟨hm0, hmlen, Hfsome⟩
                  · word
                  icases slice_advance_sub s data
                    ((b0 :: rem_tl).drop (sint.nat n)) bs dq n m hm0 hmlen
                    $$ [$Hs $Hback] with ⟨%Hmbnd, Hs, Hback⟩
                  simp only [Hmbnd.1.1, Hmbnd.1.2, Hmbnd.2, _root_.and_self, ↓reduceIte]
                  wp_auto
                  wp_for_post
                  iframe HΦ
                  iexists (slice.slice (slice.slice s w8 n s.len) w8 m (s.len - n)),
                    (((b0 :: rem_tl).drop (sint.nat n)).drop (sint.nat m)), acc
                  iframe r data Hs Hback Hr
                  ipureintro
                  rw [← Hloop, Hstep]
                  simp only [Hnum1, Hnum4, Hnum3, Hnum2, Hfsome, _root_.or_self, ↓reduceIte]
  · -- `len(data) == 0`
    have Hrem_nil : rem = [] := by
      apply List.eq_nil_of_length_eq_zero
      obtain ⟨_, _⟩ := Hslen; word
    subst Hrem_nil
    have Hdec : apply.v2Decode bs = some acc := by
      rw [← Hloop, apply.v2UnmarshalLoop.eq_def]; rfl
    iapply HΦ
    ihave Hdata := Hback $$ Hs
    simp only [Hdec]
    iframe Hdata Hr

end proof

end EtcdGrove
end Perennial
