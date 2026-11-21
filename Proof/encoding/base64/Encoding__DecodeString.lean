/-
Proof of `Encoding.DecodeString` over its translated body (`encoding/base64`, go1.27.3). Lean-first
(prove-authcrypto, 2026-11-21).
-/
module

public import Spec.encoding.base64.Encoding__DecodeString
public import Spec.encoding.base64.Encoding__DecodedLen
public import Spec.encoding.base64.Encoding__Decode
public import Proof.encoding.base64.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.encoding.base64.Assumptions]

theorem base64.Encoding.DecodeString.wp_proof
    (wp_DecodedLen : base64.Encoding.DecodedLen.spec (GF := GF) (hG := hG))
    (wp_Decode : base64.Encoding.Decode.spec (GF := GF) (hG := hG)) :
    base64.Encoding.DecodeString.spec (GF := GF) (hG := hG) := by
  intro e enc dqe s hpad hstrict hdm
  wp_start as He
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  try wp_auto
  have hL0 : 0 ≤ sint.Z (W64 (s.length : Int)) := by word
  wp_apply (wp_DecodedLen e enc dqe _ hL0) $$ He as He
  have hlen : sint.nat (W64 (s.length : Int)) = s.length := by word
  rw [hlen, hpad]
  have hdl : base64.decLen (W32 61) s.length = s.length / 4 * 3 := by
    unfold base64.decLen; rw [if_neg (by decide)]
  rw [hdl]
  wp_apply (wp_slice_make2 (V := w8) _) $$ [] as %buf ⟨Hbuf, -⟩
  · ipureintro; word
  try wp_auto
  wp_apply (wp_string_to_bytes s) as %sl ⟨Hsl, -⟩
  try wp_auto
  have hroom : 3 * (s.length / 4) ≤
      (List.replicate (sint.nat (W64 ((s.length / 4 * 3 : Nat) : Int))) (zero_val w8)).length := by
    rw [List.length_replicate]; word
  wp_apply (wp_Decode e enc dqe buf sl _ s _ hpad hstrict hdm hroom) $$ [He Hbuf Hsl]
    as %n %err ⟨%d', He, Hbuf, Hsl, %Hd⟩
  · iframe
  try wp_auto
  ihave %Hbl := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hbwf := ownSlice_wf _ _ _ $$ Hbuf
  obtain ⟨hd1, hn0, hn1, hok⟩ := Hd
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
  try wp_auto
  ihave ⟨-, Hb, -⟩ := (ownSlice_slice (W64 0) n buf (DFrac.own 1) d' ⟨by word, by word, by word⟩).1 $$ Hbuf
  iapply HΦ
  iexists _; iframe; ipureintro; exact hok

end proof

end EtcdGrove
end Perennial
