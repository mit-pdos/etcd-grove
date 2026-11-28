/-
Proof of `Encoding.Decode` over its translated body (`encoding/base64`, go1.27.3). Lean-first
(prove-authcrypto, 2026-11-21).
-/
module

public import Spec.encoding.base64.Encoding__Decode
public import Spec.encoding.base64.Encoding__decodeQuantum
public import Spec.encoding.base64.assemble32
public import Spec.encoding.base64.assemble64
public import Spec.internal.byteorder.BEPutUint32
public import Spec.internal.byteorder.BEPutUint64
public import Proof.encoding.base64.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section ite
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [go.PreSemantics]

theorem base64.ite_tt {A : Type _} (x y : A) :
    (if decide ((#true : val) = #true) = true then x else y) = x := by simp

theorem base64.ite_ft {A : Type _} (x y : A) :
    (if decide ((#false : val) = #true) = true then x else y) = y := by
  rw [if_neg]; intro h; exact false_neq_true (of_decide_eq_true h)

theorem base64.ite_ff {A : Type _} (x y : A) :
    (if decide ((#false : val) = #false) = true then x else y) = x := by simp

end ite

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.encoding.base64.Assumptions]

theorem base64.dst_split (dst : GoSlice) (d' : List w8) (n : w64)
    (h : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z dst.len) :
    (dst ↦* d' : IProp GF) ⊢ slice.slice dst w8 (W64 0) n ↦* d'.take (sint.nat n) ∗
      slice.slice dst w8 n dst.len ↦* d'.drop (sint.nat n) :=
  (ownSlice_split_all n dst (DFrac.own 1) d' h).1

theorem base64.dst_combine (dst : GoSlice) (vs1 vs2 : List w8) (n : w64) (hlen : vs1.length = sint.nat n)
    (h : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z dst.len) :
    (slice.slice dst w8 (W64 0) n ↦* vs1 ∗ slice.slice dst w8 n dst.len ↦* vs2 : IProp GF) ⊢
      dst ↦* (vs1 ++ vs2) := by
  iintro ⟨H1, H2⟩
  iapply (ownSlice_split_all n dst (DFrac.own 1) (vs1 ++ vs2) h).2
  rw [List.take_left' hlen, List.drop_left' hlen]
  iframe

set_option maxHeartbeats 4000000 in
theorem base64.Encoding.Decode.wp_proof
    (wp_decodeQuantum : base64.Encoding.decodeQuantum.spec (GF := GF) (hG := hG))
    (wp_assemble32 : base64.assemble32.spec (GF := GF) (hG := hG))
    (wp_assemble64 : base64.assemble64.spec (GF := GF) (hG := hG))
    (wp_BEPutUint32 : byteorder.BEPutUint32.spec (GF := GF) (hG := hG))
    (wp_BEPutUint64 : byteorder.BEPutUint64.spec (GF := GF) (hG := hG)) :
    base64.Encoding.Decode.spec (GF := GF) (hG := hG) := by
  intro e enc dqe dst src d s dq hpad hstrict hdm hroom
  wp_start as ⟨He, Hdst, Hsrc⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hsrc
  ihave %Hdl := ownSlice_len _ _ _ $$ Hdst
  ihave %Hsw := ownSlice_wf _ _ _ $$ Hsrc
  ihave %Hdw := ownSlice_wf _ _ _ $$ Hdst
  have hL : sint.Z src.len = s.length := by have := Hsl.1; word
  have hD : sint.Z dst.len = d.length := by have := Hdl.1; word
  try wp_auto
  wp_if_destruct
  · -- nothing to decode
    try wp_auto
    iapply HΦ; iexists d; iframe; ipureintro
    have hs0 : s = [] := List.eq_nil_of_length_eq_zero (by
      have := Hsl.1
      first | word | (have := of_decide_eq_true Hif.symm; word) | (have := of_decide_eq_true Hif; word))
    refine ⟨rfl, by word, by word, fun _ => ⟨fun _ => by rw [hs0]; simp [_root_.Perennial.encoding.base64.dropNL, base64.b64Ok], fun _ => rfl⟩⟩
  · icases base64.enc_open e enc dqe $$ He with ⟨%Hnn, Hf⟩
    icases Hf with ⟨Henc, Hdm, Hpad, Hstrict⟩
    try wp_auto
    have hcbf : ∀ x : w8, 0 ≤ sint.Z (W64 (uint.Z x)) ∧ sint.Z (W64 (uint.Z x)) < 256 := by
      intro x; have := x.isLt; constructor <;> word
    have hidxf : ∀ x : w8, (sint.Z (W64 (uint.Z x))).toNat = x.toNat := by
      intro x; have := x.isLt; word
    ihave HI : (∃ (n si : w64) (d' : List w8),
        "n" ∷ n_ptr ↦ n ∗ "si" ∷ si_ptr ↦ si ∗ "err" ∷ err_ptr ↦ GoInterface.nil ∗ "Hdst" ∷ dst ↦* d' ∗
        "%Hinv'" ∷ ⌜d'.length = d.length ∧ 0 ≤ sint.Z si ∧ sint.Z si ≤ s.length ∧ 0 ≤ sint.Z n ∧
          sint.Z n ≤ d.length ∧ ((∃ k : Nat, sint.Z n = 3 * k ∧ 4 * k ≤ sint.Z si) ∨ sint.Z si = s.length) ∧
          (base64.decOk enc → (base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL s) ↔
            base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si)))))⌝ : IProp GF)
        $$ [n si err Hdst]
    · iexists W64 0, W64 0, d; iframe; ipureintro
      refine ⟨rfl, by word, by word, by word, by word, .inl ⟨0, by word, by word⟩,
        fun _ => by rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]⟩
    wp_join (Q := fun v => iprop(
        (∃ (n si : w64) (d' : List w8), "He" ∷ e ↦{dqe} enc ∗ "n" ∷ n_ptr ↦ n ∗ "si" ∷ si_ptr ↦ si ∗
          "err" ∷ err_ptr ↦ GoInterface.nil ∗ "Hdst" ∷ dst ↦* d' ∗ "Hsrc" ∷ src ↦*{dq} s ∗
          "src" ∷ src_ptr ↦ src ∗ "dst" ∷ dst_ptr ↦ dst ∗ "enc" ∷ enc_ptr ↦ e ∗
          "%Hv" ∷ ⌜v = executeVal⌝ ∗ "%Hinv'" ∷ ⌜d'.length = d.length ∧ 0 ≤ sint.Z si ∧ sint.Z si ≤ s.length ∧ 0 ≤ sint.Z n ∧
          sint.Z n ≤ d.length ∧ ((∃ k : Nat, sint.Z n = 3 * k ∧ 4 * k ≤ sint.Z si) ∨ sint.Z si = s.length) ∧
          (base64.decOk enc → (base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL s) ↔
            base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si)))))⌝) ∨
        (∃ (n : w64) (err : GoInterface) (d' : List w8), "He" ∷ e ↦{dqe} enc ∗ "n" ∷ n_ptr ↦ n ∗
          "err" ∷ err_ptr ↦ err ∗ "Hdst" ∷ dst ↦* d' ∗ "Hsrc" ∷ src ↦*{dq} s ∗
          "%Hret" ∷ ⌜v = returnVal #() ∧ d'.length = d.length ∧ 0 ≤ sint.Z n ∧ sint.Z n ≤ d.length ∧
            (base64.decOk enc → (err = GoInterface.nil ↔ base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL s)))⌝))) at next
      with [-HΦ]
    · wp_for HI
      by_cases hc1 : sint.Z (W64 8) ≤ sint.Z (src.len - si)
      · rw [decide_eq_true hc1]
        try wp_auto
        by_cases hc2 : sint.Z (W64 8) ≤ sint.Z (dst.len - n)
        · rw [decide_eq_true hc2, base64.ite_tt]
          have hw : sint.Z si + 8 ≤ s.length := by
            have h := hc1; have := Hinv'.2.2.1; word
          have hnw : sint.Z n + 8 ≤ d.length := by
            have h := hc2; have := Hinv'.2.2.2.2.1
            have := Hinv'.1; word
          have hsb : 0 ≤ sint.Z si ∧ sint.Z si ≤ sint.Z (si + W64 8) ∧ sint.Z (si + W64 8) ≤ sint.Z src.cap := by
            have := Hinv'.2.1; have := Hsw.2; constructor <;> (try constructor) <;> word
          obtain ⟨x0, hx0⟩ : ∃ x, s[(sint.Z si + sint.Z (W64 0)).toNat]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by word)⟩
          have hi0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z (si + W64 8 - si) := by constructor <;> word
          have hp0 : 0 ≤ sint.Z si + sint.Z (W64 0) := by word
          obtain ⟨x1, hx1⟩ : ∃ x, s[(sint.Z si + sint.Z (W64 1)).toNat]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by word)⟩
          have hi1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z (si + W64 8 - si) := by constructor <;> word
          have hp1 : 0 ≤ sint.Z si + sint.Z (W64 1) := by word
          obtain ⟨x2, hx2⟩ : ∃ x, s[(sint.Z si + sint.Z (W64 2)).toNat]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by word)⟩
          have hi2 : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z (si + W64 8 - si) := by constructor <;> word
          have hp2 : 0 ≤ sint.Z si + sint.Z (W64 2) := by word
          obtain ⟨x3, hx3⟩ : ∃ x, s[(sint.Z si + sint.Z (W64 3)).toNat]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by word)⟩
          have hi3 : 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) < sint.Z (si + W64 8 - si) := by constructor <;> word
          have hp3 : 0 ≤ sint.Z si + sint.Z (W64 3) := by word
          obtain ⟨x4, hx4⟩ : ∃ x, s[(sint.Z si + sint.Z (W64 4)).toNat]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by word)⟩
          have hi4 : 0 ≤ sint.Z (W64 4) ∧ sint.Z (W64 4) < sint.Z (si + W64 8 - si) := by constructor <;> word
          have hp4 : 0 ≤ sint.Z si + sint.Z (W64 4) := by word
          obtain ⟨x5, hx5⟩ : ∃ x, s[(sint.Z si + sint.Z (W64 5)).toNat]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by word)⟩
          have hi5 : 0 ≤ sint.Z (W64 5) ∧ sint.Z (W64 5) < sint.Z (si + W64 8 - si) := by constructor <;> word
          have hp5 : 0 ≤ sint.Z si + sint.Z (W64 5) := by word
          obtain ⟨x6, hx6⟩ : ∃ x, s[(sint.Z si + sint.Z (W64 6)).toNat]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by word)⟩
          have hi6 : 0 ≤ sint.Z (W64 6) ∧ sint.Z (W64 6) < sint.Z (si + W64 8 - si) := by constructor <;> word
          have hp6 : 0 ≤ sint.Z si + sint.Z (W64 6) := by word
          obtain ⟨x7, hx7⟩ : ∃ x, s[(sint.Z si + sint.Z (W64 7)).toNat]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by word)⟩
          have hi7 : 0 ≤ sint.Z (W64 7) ∧ sint.Z (W64 7) < sint.Z (si + W64 8 - si) := by constructor <;> word
          have hp7 : 0 ≤ sint.Z si + sint.Z (W64 7) := by word
          try wp_auto

          rw [ite_eq_left_of_eq_true _ _ (eq_true hsb)]
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true hi0), base64.sliceIndexRef_slice]
          wp_apply (wp_load_slice_index src _ s dq x0 hp0) $$ [Hsrc] as Hsrc
          · iframe; ipureintro; exact hx0
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true (hcbf x0))]
          wp_apply (base64.wp_load_arr _ 256 _ dqe _ (hcbf x0)) $$ Hdm as Hdm
          rw [hidxf x0]
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true hi1), base64.sliceIndexRef_slice]
          wp_apply (wp_load_slice_index src _ s dq x1 hp1) $$ [Hsrc] as Hsrc
          · iframe; ipureintro; exact hx1
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true (hcbf x1))]
          wp_apply (base64.wp_load_arr _ 256 _ dqe _ (hcbf x1)) $$ Hdm as Hdm
          rw [hidxf x1]
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true hi2), base64.sliceIndexRef_slice]
          wp_apply (wp_load_slice_index src _ s dq x2 hp2) $$ [Hsrc] as Hsrc
          · iframe; ipureintro; exact hx2
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true (hcbf x2))]
          wp_apply (base64.wp_load_arr _ 256 _ dqe _ (hcbf x2)) $$ Hdm as Hdm
          rw [hidxf x2]
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true hi3), base64.sliceIndexRef_slice]
          wp_apply (wp_load_slice_index src _ s dq x3 hp3) $$ [Hsrc] as Hsrc
          · iframe; ipureintro; exact hx3
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true (hcbf x3))]
          wp_apply (base64.wp_load_arr _ 256 _ dqe _ (hcbf x3)) $$ Hdm as Hdm
          rw [hidxf x3]
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true hi4), base64.sliceIndexRef_slice]
          wp_apply (wp_load_slice_index src _ s dq x4 hp4) $$ [Hsrc] as Hsrc
          · iframe; ipureintro; exact hx4
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true (hcbf x4))]
          wp_apply (base64.wp_load_arr _ 256 _ dqe _ (hcbf x4)) $$ Hdm as Hdm
          rw [hidxf x4]
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true hi5), base64.sliceIndexRef_slice]
          wp_apply (wp_load_slice_index src _ s dq x5 hp5) $$ [Hsrc] as Hsrc
          · iframe; ipureintro; exact hx5
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true (hcbf x5))]
          wp_apply (base64.wp_load_arr _ 256 _ dqe _ (hcbf x5)) $$ Hdm as Hdm
          rw [hidxf x5]
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true hi6), base64.sliceIndexRef_slice]
          wp_apply (wp_load_slice_index src _ s dq x6 hp6) $$ [Hsrc] as Hsrc
          · iframe; ipureintro; exact hx6
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true (hcbf x6))]
          wp_apply (base64.wp_load_arr _ 256 _ dqe _ (hcbf x6)) $$ Hdm as Hdm
          rw [hidxf x6]
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true hi7), base64.sliceIndexRef_slice]
          wp_apply (wp_load_slice_index src _ s dq x7 hp7) $$ [Hsrc] as Hsrc
          · iframe; ipureintro; exact hx7
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true (hcbf x7))]
          wp_apply (base64.wp_load_arr _ 256 _ dqe _ (hcbf x7)) $$ Hdm as Hdm
          rw [hidxf x7]
          try wp_auto
          wp_apply (wp_assemble64 _ _ _ _ _ _ _ _) as %dn %ok %Hok
          try wp_auto
          wp_if_destruct
          · -- a non-symbol: one quantum
            have hqa : 0 ≤ sint.Z si := Hinv'.2.1
            have hqb : sint.Z si ≤ s.length := Hinv'.2.2.1
            have hsp : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z dst.len := by
              have := Hinv'.2.2.2.1; have := Hinv'.2.2.2.2.1; have := Hinv'.1; constructor <;> word
            have hsl1 : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z dst.len ∧ sint.Z dst.len ≤ sint.Z dst.cap :=
              ⟨hsp.1, hsp.2, Hdw.2⟩
            have hcomb : (d'.take (sint.nat n)).length = sint.nat n := by
              simp only [List.length_take]; have := Hinv'.1; have := Hinv'.2.2.2.2.1; word
            wp_pures
            try wp_auto
            rw [ite_eq_left_of_eq_true _ _ (eq_true hsl1)]
            ihave ⟨Hd1, Hd2⟩ := base64.dst_split dst d' n hsp $$ Hdst
            ihave He : e ↦{dqe} enc $$ [Henc Hdm Hpad Hstrict]
            · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
            have hroom' : 3 * ((s.length - sint.nat si) / 4) ≤ (d'.drop (sint.nat n)).length := by
              rw [List.length_drop]
              have := Hinv'.1
              rcases Hinv'.2.2.2.2.2.1 with ⟨k, hk1, hk2⟩ | h
              · have hn' : sint.nat n = 3 * k := by word
                have hs' : 4 * k ≤ sint.nat si := by word
                have hsl : sint.nat si ≤ s.length := by word
                have hdl' : d'.length = d.length := Hinv'.1
                omega
              · have : s.length - sint.nat si = 0 := by word
                rw [this]; omega
            try wp_auto
            wp_bind (App (App (App (Val _) (Val _)) (Val _)) (Val _))
            iapply (wp_decodeQuantum e enc dqe _ src (d'.drop (sint.nat n)) s dq si hpad hstrict hdm
                hqa hqb hroom') $$ [He Hd2 Hsrc]
            · iframe
            inext
            iintro %si' %ninc %qerr ⟨%d2, He, Hd2, Hsrc, %Hq⟩
            obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7⟩ := Hq
            ihave Hdst := base64.dst_combine dst (d'.take (sint.nat n)) d2 n hcomb hsp $$ [Hd1 Hd2]
            · iframe
            icases base64.enc_open e enc dqe $$ He with ⟨-, Hf⟩
            icases Hf with ⟨Henc, Hdm, Hpad, Hstrict⟩
            try wp_auto
            have hlen' : (d'.take (sint.nat n) ++ d2).length = d.length := by
              rw [List.length_append, List.length_take, hq1, List.length_drop]
              have := Hinv'.1; have := Hinv'.2.2.2.2.1; word
            have hnb : sint.Z n + sint.Z ninc ≤ d.length := by
              have := Hinv'.1
              rcases Hinv'.2.2.2.2.2.1 with ⟨k, hk1, hk2⟩ | h
              · have h3 : 3 * (s.length / 4) ≤ d.length := hroom
                have : sint.Z ninc ≤ 3 * ((sint.Z si' - sint.Z si) / 4) := hq5
                have hsl : sint.Z si' ≤ s.length := hq3
                omega
              · have : sint.Z si' = sint.Z si := by omega
                have : sint.Z ninc ≤ 0 := by rw [this] at hq5; simpa using hq5
                have := Hinv'.2.2.2.2.1; omega
            rcases qerr with qei | _
            · -- the quantum's error: returned
              try wp_auto
              wp_for_post
              iright; iexists _, _, _
              isplitl [Henc Hdm Hpad Hstrict]
              · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
              iframe; ipureintro
              refine ⟨rfl, hlen', by word, by word, fun hok => ⟨fun h => absurd h (by intro h'; cases h'), fun hb => ?_⟩⟩
              exact absurd ((Hinv'.2.2.2.2.2.2 hok).1 hb) ((hq7 hok).2 (by intro h'; cases h'))
            · -- no error: on
              try wp_auto
              wp_for_post
              iframe; iexists n + ninc, si', _; iframe; ipureintro
              refine ⟨hlen', by word, hq3, by word, by word, ?_, fun hok => ?_⟩
              · rcases hq6 rfl with ⟨h3, h4⟩ | h
                · rcases Hinv'.2.2.2.2.2.1 with ⟨k, hk1, hk2⟩ | h'
                  · exact .inl ⟨k + 1, by word, by word⟩
                  · exfalso; omega
                · exact .inr h
              · exact (Hinv'.2.2.2.2.2.2 hok).trans (base64.quantumOk_iff ((hq7 hok).1 rfl))
          · -- all symbols: stored at once
            have hor := base64.not_of_true_eq_not_decide Hok
            obtain ⟨h06, h7⟩ := base64.or_ne_ff hor
            obtain ⟨h05, h6⟩ := base64.or_ne_ff h06
            obtain ⟨h04, h5⟩ := base64.or_ne_ff h05
            obtain ⟨h03, h4⟩ := base64.or_ne_ff h04
            obtain ⟨h02, h3⟩ := base64.or_ne_ff h03
            obtain ⟨h01, h2⟩ := base64.or_ne_ff h02
            obtain ⟨h0, h1⟩ := base64.or_ne_ff h01
            have hs0 := fun (hok : base64.decOk enc) => base64.decOk_sym_of_ne hok x0 h0
            have hx0' : s[sint.nat si]? = some x0 := by
              rw [show sint.nat si = (sint.Z si + sint.Z (W64 0)).toNat by word]; exact hx0
            have hs1 := fun (hok : base64.decOk enc) => base64.decOk_sym_of_ne hok x1 h1
            have hx1' : s[sint.nat si + 1]? = some x1 := by
              rw [show sint.nat si + 1 = (sint.Z si + sint.Z (W64 1)).toNat by word]; exact hx1
            have hs2 := fun (hok : base64.decOk enc) => base64.decOk_sym_of_ne hok x2 h2
            have hx2' : s[sint.nat si + 2]? = some x2 := by
              rw [show sint.nat si + 2 = (sint.Z si + sint.Z (W64 2)).toNat by word]; exact hx2
            have hs3 := fun (hok : base64.decOk enc) => base64.decOk_sym_of_ne hok x3 h3
            have hx3' : s[sint.nat si + 3]? = some x3 := by
              rw [show sint.nat si + 3 = (sint.Z si + sint.Z (W64 3)).toNat by word]; exact hx3
            have hs4 := fun (hok : base64.decOk enc) => base64.decOk_sym_of_ne hok x4 h4
            have hx4' : s[sint.nat si + 4]? = some x4 := by
              rw [show sint.nat si + 4 = (sint.Z si + sint.Z (W64 4)).toNat by word]; exact hx4
            have hs5 := fun (hok : base64.decOk enc) => base64.decOk_sym_of_ne hok x5 h5
            have hx5' : s[sint.nat si + 4 + 1]? = some x5 := by
              rw [show sint.nat si + 4 + 1 = (sint.Z si + sint.Z (W64 5)).toNat by word]; exact hx5
            have hs6 := fun (hok : base64.decOk enc) => base64.decOk_sym_of_ne hok x6 h6
            have hx6' : s[sint.nat si + 4 + 2]? = some x6 := by
              rw [show sint.nat si + 4 + 2 = (sint.Z si + sint.Z (W64 6)).toNat by word]; exact hx6
            have hs7 := fun (hok : base64.decOk enc) => base64.decOk_sym_of_ne hok x7 h7
            have hx7' : s[sint.nat si + 4 + 3]? = some x7 := by
              rw [show sint.nat si + 4 + 3 = (sint.Z si + sint.Z (W64 7)).toNat by word]; exact hx7
            have hsp : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z dst.len := by
              have := Hinv'.2.2.2.1; have := Hinv'.2.2.2.2.1; have := Hinv'.1; constructor <;> word
            have hsl1 : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z dst.len ∧ sint.Z dst.len ≤ sint.Z dst.cap :=
              ⟨hsp.1, hsp.2, Hdw.2⟩
            have hcomb : (d'.take (sint.nat n)).length = sint.nat n := by
              simp only [List.length_take]; have := Hinv'.1; have := Hinv'.2.2.2.2.1; word
            have hbl : 8 ≤ (d'.drop (sint.nat n)).length := by
              rw [List.length_drop]; have := Hinv'.1; word
            try wp_auto
            rw [ite_eq_left_of_eq_true _ _ (eq_true hsl1)]
            ihave ⟨Hd1, Hd2⟩ := base64.dst_split dst d' n hsp $$ Hdst
            try wp_auto
            wp_bind (App (App (Val _) (Val _)) (Val _))
            iapply (wp_BEPutUint64 _ (d'.drop (sint.nat n)) dn hbl) $$ [Hd2]
            · iframe
            inext
            iintro ⟨%bs', Hd2, %hbs'⟩
            ihave Hdst := base64.dst_combine dst (d'.take (sint.nat n)) bs' n hcomb hsp $$ [Hd1 Hd2]
            · iframe
            try wp_auto
            wp_for_post
            iframe; iexists n + W64 6, si + W64 8, _; iframe; ipureintro
            refine ⟨by rw [List.length_append, List.length_take, hbs', List.length_drop]; have := Hinv'.1; have := Hinv'.2.2.2.2.1; word,
              by word, by word, by word, by word, ?_, fun hok => ?_⟩
            · rcases Hinv'.2.2.2.2.2.1 with ⟨k, hk1, hk2⟩ | h
              · exact .inl ⟨k + 2, by word, by word⟩
              · exfalso; omega
            · refine (Hinv'.2.2.2.2.2.2 hok).trans ?_
              rw [show sint.nat (si + W64 8) = sint.nat si + 4 + 4 by word]
              exact (base64.b64Ok_drop_sym4 hok s _ x0 x1 x2 x3 hx0' hx1' hx2' hx3' (hs0 hok) (hs1 hok) (hs2 hok) (hs3 hok)).trans
                (base64.b64Ok_drop_sym4 hok s _ x4 x5 x6 x7 hx4' hx5' hx6' hx7' (hs4 hok) (hs5 hok) (hs6 hok) (hs7 hok))
        · rw [decide_eq_false hc2]
          try wp_auto
          rw [base64.ite_ft, base64.ite_ff]
          try wp_auto
          ileft; iexists n, si, d'
          isplitl [Henc Hdm Hpad Hstrict]
          · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
          iframe; ipureintro
          exact ⟨by first | trivial | rfl, Hinv'⟩
      · rw [decide_eq_false hc1]
        try wp_auto
        rw [base64.ite_ft, base64.ite_ff]
        try wp_auto
        ileft; iexists n, si, d'
        isplitl [Henc Hdm Hpad Hstrict]
        · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
        iframe; ipureintro
        exact ⟨by first | trivial | rfl, Hinv'⟩
    · iintro HQ
      icases HQ with (⟨%n, %si, %d', He, n, si, err, Hdst, Hsrc, src, dst, enc, %Hv, %Hinv'⟩ |
        ⟨%n, %err', %d', He, n, err, Hdst, Hsrc, %Hret⟩)
      · subst Hv
        icases base64.enc_open e enc dqe $$ He with ⟨-, Hf⟩
        icases Hf with ⟨Henc, Hdm, Hpad, Hstrict⟩
        try wp_auto
        ihave HI : (∃ (n si : w64) (d' : List w8),
            "n" ∷ n_ptr ↦ n ∗ "si" ∷ si_ptr ↦ si ∗ "err" ∷ err_ptr ↦ GoInterface.nil ∗ "Hdst" ∷ dst ↦* d' ∗
            "%Hinv'" ∷ ⌜d'.length = d.length ∧ 0 ≤ sint.Z si ∧ sint.Z si ≤ s.length ∧ 0 ≤ sint.Z n ∧
              sint.Z n ≤ d.length ∧ ((∃ k : Nat, sint.Z n = 3 * k ∧ 4 * k ≤ sint.Z si) ∨ sint.Z si = s.length) ∧
              (base64.decOk enc → (base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL s) ↔
                base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si)))))⌝ : IProp GF)
            $$ [n si err Hdst]
        · iexists _, _, _; iframe; ipureintro; exact Hinv'
        wp_join (Q := fun v => iprop(
            (∃ (n si : w64) (d' : List w8), "He" ∷ e ↦{dqe} enc ∗ "n" ∷ n_ptr ↦ n ∗ "si" ∷ si_ptr ↦ si ∗
              "err" ∷ err_ptr ↦ GoInterface.nil ∗ "Hdst" ∷ dst ↦* d' ∗ "Hsrc" ∷ src ↦*{dq} s ∗
              "src" ∷ src_ptr ↦ src ∗ "dst" ∷ dst_ptr ↦ dst ∗ "enc" ∷ enc_ptr ↦ e ∗
              "%Hv" ∷ ⌜v = executeVal⌝ ∗ "%Hinv'" ∷ ⌜d'.length = d.length ∧ 0 ≤ sint.Z si ∧ sint.Z si ≤ s.length ∧ 0 ≤ sint.Z n ∧
              sint.Z n ≤ d.length ∧ ((∃ k : Nat, sint.Z n = 3 * k ∧ 4 * k ≤ sint.Z si) ∨ sint.Z si = s.length) ∧
              (base64.decOk enc → (base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL s) ↔
                base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si)))))⌝) ∨
            (∃ (n : w64) (err : GoInterface) (d' : List w8), "He" ∷ e ↦{dqe} enc ∗ "n" ∷ n_ptr ↦ n ∗
              "err" ∷ err_ptr ↦ err ∗ "Hdst" ∷ dst ↦* d' ∗ "Hsrc" ∷ src ↦*{dq} s ∗
              "%Hret" ∷ ⌜v = returnVal #() ∧ d'.length = d.length ∧ 0 ≤ sint.Z n ∧ sint.Z n ≤ d.length ∧
                (base64.decOk enc → (err = GoInterface.nil ↔ base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL s)))⌝))) at next
          with [-HΦ]
        · wp_for HI
          by_cases hc1 : sint.Z (W64 4) ≤ sint.Z (src.len - si)
          · rw [decide_eq_true hc1]
            try wp_auto
            by_cases hc2 : sint.Z (W64 4) ≤ sint.Z (dst.len - n)
            · rw [decide_eq_true hc2, base64.ite_tt]
              have hw : sint.Z si + 4 ≤ s.length := by
                have h := hc1; have := Hinv'.2.2.1; word
              have hnw : sint.Z n + 4 ≤ d.length := by
                have h := hc2; have := Hinv'.2.2.2.2.1
                have := Hinv'.1; word
              have hsb : 0 ≤ sint.Z si ∧ sint.Z si ≤ sint.Z (si + W64 4) ∧ sint.Z (si + W64 4) ≤ sint.Z src.cap := by
                have := Hinv'.2.1; have := Hsw.2; constructor <;> (try constructor) <;> word
              obtain ⟨x0, hx0⟩ : ∃ x, s[(sint.Z si + sint.Z (W64 0)).toNat]? = some x :=
                ⟨_, List.getElem?_eq_getElem (by word)⟩
              have hi0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z (si + W64 4 - si) := by constructor <;> word
              have hp0 : 0 ≤ sint.Z si + sint.Z (W64 0) := by word
              obtain ⟨x1, hx1⟩ : ∃ x, s[(sint.Z si + sint.Z (W64 1)).toNat]? = some x :=
                ⟨_, List.getElem?_eq_getElem (by word)⟩
              have hi1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z (si + W64 4 - si) := by constructor <;> word
              have hp1 : 0 ≤ sint.Z si + sint.Z (W64 1) := by word
              obtain ⟨x2, hx2⟩ : ∃ x, s[(sint.Z si + sint.Z (W64 2)).toNat]? = some x :=
                ⟨_, List.getElem?_eq_getElem (by word)⟩
              have hi2 : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z (si + W64 4 - si) := by constructor <;> word
              have hp2 : 0 ≤ sint.Z si + sint.Z (W64 2) := by word
              obtain ⟨x3, hx3⟩ : ∃ x, s[(sint.Z si + sint.Z (W64 3)).toNat]? = some x :=
                ⟨_, List.getElem?_eq_getElem (by word)⟩
              have hi3 : 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) < sint.Z (si + W64 4 - si) := by constructor <;> word
              have hp3 : 0 ≤ sint.Z si + sint.Z (W64 3) := by word
              try wp_auto

              rw [ite_eq_left_of_eq_true _ _ (eq_true hsb)]
              try wp_auto
              rw [ite_eq_left_of_eq_true _ _ (eq_true hi0), base64.sliceIndexRef_slice]
              wp_apply (wp_load_slice_index src _ s dq x0 hp0) $$ [Hsrc] as Hsrc
              · iframe; ipureintro; exact hx0
              try wp_auto
              rw [ite_eq_left_of_eq_true _ _ (eq_true (hcbf x0))]
              wp_apply (base64.wp_load_arr _ 256 _ dqe _ (hcbf x0)) $$ Hdm as Hdm
              rw [hidxf x0]
              try wp_auto
              rw [ite_eq_left_of_eq_true _ _ (eq_true hi1), base64.sliceIndexRef_slice]
              wp_apply (wp_load_slice_index src _ s dq x1 hp1) $$ [Hsrc] as Hsrc
              · iframe; ipureintro; exact hx1
              try wp_auto
              rw [ite_eq_left_of_eq_true _ _ (eq_true (hcbf x1))]
              wp_apply (base64.wp_load_arr _ 256 _ dqe _ (hcbf x1)) $$ Hdm as Hdm
              rw [hidxf x1]
              try wp_auto
              rw [ite_eq_left_of_eq_true _ _ (eq_true hi2), base64.sliceIndexRef_slice]
              wp_apply (wp_load_slice_index src _ s dq x2 hp2) $$ [Hsrc] as Hsrc
              · iframe; ipureintro; exact hx2
              try wp_auto
              rw [ite_eq_left_of_eq_true _ _ (eq_true (hcbf x2))]
              wp_apply (base64.wp_load_arr _ 256 _ dqe _ (hcbf x2)) $$ Hdm as Hdm
              rw [hidxf x2]
              try wp_auto
              rw [ite_eq_left_of_eq_true _ _ (eq_true hi3), base64.sliceIndexRef_slice]
              wp_apply (wp_load_slice_index src _ s dq x3 hp3) $$ [Hsrc] as Hsrc
              · iframe; ipureintro; exact hx3
              try wp_auto
              rw [ite_eq_left_of_eq_true _ _ (eq_true (hcbf x3))]
              wp_apply (base64.wp_load_arr _ 256 _ dqe _ (hcbf x3)) $$ Hdm as Hdm
              rw [hidxf x3]
              try wp_auto
              wp_apply (wp_assemble32 _ _ _ _) as %dn %ok %Hok
              try wp_auto
              wp_if_destruct
              · -- a non-symbol: one quantum
                have hqa : 0 ≤ sint.Z si := Hinv'.2.1
                have hqb : sint.Z si ≤ s.length := Hinv'.2.2.1
                have hsp : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z dst.len := by
                  have := Hinv'.2.2.2.1; have := Hinv'.2.2.2.2.1; have := Hinv'.1; constructor <;> word
                have hsl1 : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z dst.len ∧ sint.Z dst.len ≤ sint.Z dst.cap :=
                  ⟨hsp.1, hsp.2, Hdw.2⟩
                have hcomb : (d'.take (sint.nat n)).length = sint.nat n := by
                  simp only [List.length_take]; have := Hinv'.1; have := Hinv'.2.2.2.2.1; word
                wp_pures
                try wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true hsl1)]
                ihave ⟨Hd1, Hd2⟩ := base64.dst_split dst d' n hsp $$ Hdst
                ihave He : e ↦{dqe} enc $$ [Henc Hdm Hpad Hstrict]
                · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
                have hroom' : 3 * ((s.length - sint.nat si) / 4) ≤ (d'.drop (sint.nat n)).length := by
                  rw [List.length_drop]
                  have := Hinv'.1
                  rcases Hinv'.2.2.2.2.2.1 with ⟨k, hk1, hk2⟩ | h
                  · have hn' : sint.nat n = 3 * k := by word
                    have hs' : 4 * k ≤ sint.nat si := by word
                    have hsl : sint.nat si ≤ s.length := by word
                    have hdl' : d'.length = d.length := Hinv'.1
                    omega
                  · have : s.length - sint.nat si = 0 := by word
                    rw [this]; omega
                try wp_auto
                wp_bind (App (App (App (Val _) (Val _)) (Val _)) (Val _))
                iapply (wp_decodeQuantum e enc dqe _ src (d'.drop (sint.nat n)) s dq si hpad hstrict hdm
                    hqa hqb hroom') $$ [He Hd2 Hsrc]
                · iframe
                inext
                iintro %si' %ninc %qerr ⟨%d2, He, Hd2, Hsrc, %Hq⟩
                obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7⟩ := Hq
                ihave Hdst := base64.dst_combine dst (d'.take (sint.nat n)) d2 n hcomb hsp $$ [Hd1 Hd2]
                · iframe
                icases base64.enc_open e enc dqe $$ He with ⟨-, Hf⟩
                icases Hf with ⟨Henc, Hdm, Hpad, Hstrict⟩
                try wp_auto
                have hlen' : (d'.take (sint.nat n) ++ d2).length = d.length := by
                  rw [List.length_append, List.length_take, hq1, List.length_drop]
                  have := Hinv'.1; have := Hinv'.2.2.2.2.1; word
                have hnb : sint.Z n + sint.Z ninc ≤ d.length := by
                  have := Hinv'.1
                  rcases Hinv'.2.2.2.2.2.1 with ⟨k, hk1, hk2⟩ | h
                  · have h3 : 3 * (s.length / 4) ≤ d.length := hroom
                    have : sint.Z ninc ≤ 3 * ((sint.Z si' - sint.Z si) / 4) := hq5
                    have hsl : sint.Z si' ≤ s.length := hq3
                    omega
                  · have : sint.Z si' = sint.Z si := by omega
                    have : sint.Z ninc ≤ 0 := by rw [this] at hq5; simpa using hq5
                    have := Hinv'.2.2.2.2.1; omega
                rcases qerr with qei | _
                · -- the quantum's error: returned
                  try wp_auto
                  wp_for_post
                  iright; iexists _, _, _
                  isplitl [Henc Hdm Hpad Hstrict]
                  · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
                  iframe; ipureintro
                  refine ⟨rfl, hlen', by word, by word, fun hok => ⟨fun h => absurd h (by intro h'; cases h'), fun hb => ?_⟩⟩
                  exact absurd ((Hinv'.2.2.2.2.2.2 hok).1 hb) ((hq7 hok).2 (by intro h'; cases h'))
                · -- no error: on
                  try wp_auto
                  wp_for_post
                  iframe; iexists n + ninc, si', _; iframe; ipureintro
                  refine ⟨hlen', by word, hq3, by word, by word, ?_, fun hok => ?_⟩
                  · rcases hq6 rfl with ⟨h3, h4⟩ | h
                    · rcases Hinv'.2.2.2.2.2.1 with ⟨k, hk1, hk2⟩ | h'
                      · exact .inl ⟨k + 1, by word, by word⟩
                      · exfalso; omega
                    · exact .inr h
                  · exact (Hinv'.2.2.2.2.2.2 hok).trans (base64.quantumOk_iff ((hq7 hok).1 rfl))
              · -- all symbols: stored at once
                have hor := base64.not_of_true_eq_not_decide Hok
                have h03 := hor
                obtain ⟨h02, h3⟩ := base64.or_ne_ff h03
                obtain ⟨h01, h2⟩ := base64.or_ne_ff h02
                obtain ⟨h0, h1⟩ := base64.or_ne_ff h01
                have hs0 := fun (hok : base64.decOk enc) => base64.decOk_sym_of_ne hok x0 h0
                have hx0' : s[sint.nat si]? = some x0 := by
                  rw [show sint.nat si = (sint.Z si + sint.Z (W64 0)).toNat by word]; exact hx0
                have hs1 := fun (hok : base64.decOk enc) => base64.decOk_sym_of_ne hok x1 h1
                have hx1' : s[sint.nat si + 1]? = some x1 := by
                  rw [show sint.nat si + 1 = (sint.Z si + sint.Z (W64 1)).toNat by word]; exact hx1
                have hs2 := fun (hok : base64.decOk enc) => base64.decOk_sym_of_ne hok x2 h2
                have hx2' : s[sint.nat si + 2]? = some x2 := by
                  rw [show sint.nat si + 2 = (sint.Z si + sint.Z (W64 2)).toNat by word]; exact hx2
                have hs3 := fun (hok : base64.decOk enc) => base64.decOk_sym_of_ne hok x3 h3
                have hx3' : s[sint.nat si + 3]? = some x3 := by
                  rw [show sint.nat si + 3 = (sint.Z si + sint.Z (W64 3)).toNat by word]; exact hx3
                have hsp : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z dst.len := by
                  have := Hinv'.2.2.2.1; have := Hinv'.2.2.2.2.1; have := Hinv'.1; constructor <;> word
                have hsl1 : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z dst.len ∧ sint.Z dst.len ≤ sint.Z dst.cap :=
                  ⟨hsp.1, hsp.2, Hdw.2⟩
                have hcomb : (d'.take (sint.nat n)).length = sint.nat n := by
                  simp only [List.length_take]; have := Hinv'.1; have := Hinv'.2.2.2.2.1; word
                have hbl : 4 ≤ (d'.drop (sint.nat n)).length := by
                  rw [List.length_drop]; have := Hinv'.1; word
                try wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true hsl1)]
                ihave ⟨Hd1, Hd2⟩ := base64.dst_split dst d' n hsp $$ Hdst
                try wp_auto
                wp_bind (App (App (Val _) (Val _)) (Val _))
                iapply (wp_BEPutUint32 _ (d'.drop (sint.nat n)) dn hbl) $$ [Hd2]
                · iframe
                inext
                iintro ⟨%bs', Hd2, %hbs'⟩
                ihave Hdst := base64.dst_combine dst (d'.take (sint.nat n)) bs' n hcomb hsp $$ [Hd1 Hd2]
                · iframe
                try wp_auto
                wp_for_post
                iframe; iexists n + W64 3, si + W64 4, _; iframe; ipureintro
                refine ⟨by rw [List.length_append, List.length_take, hbs', List.length_drop]; have := Hinv'.1; have := Hinv'.2.2.2.2.1; word,
                  by word, by word, by word, by word, ?_, fun hok => ?_⟩
                · rcases Hinv'.2.2.2.2.2.1 with ⟨k, hk1, hk2⟩ | h
                  · exact .inl ⟨k + 1, by word, by word⟩
                  · exfalso; omega
                · refine (Hinv'.2.2.2.2.2.2 hok).trans ?_
                  rw [show sint.nat (si + W64 4) = sint.nat si + 4 by word]
                  exact base64.b64Ok_drop_sym4 hok s _ x0 x1 x2 x3 hx0' hx1' hx2' hx3' (hs0 hok) (hs1 hok) (hs2 hok) (hs3 hok)
            · rw [decide_eq_false hc2]
              try wp_auto
              rw [base64.ite_ft, base64.ite_ff]
              try wp_auto
              ileft; iexists n, si, d'
              isplitl [Henc Hdm Hpad Hstrict]
              · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
              iframe; ipureintro
              exact ⟨by first | trivial | rfl, Hinv'⟩
          · rw [decide_eq_false hc1]
            try wp_auto
            rw [base64.ite_ft, base64.ite_ff]
            try wp_auto
            ileft; iexists n, si, d'
            isplitl [Henc Hdm Hpad Hstrict]
            · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
            iframe; ipureintro
            exact ⟨by first | trivial | rfl, Hinv'⟩
        · iintro HQ
          icases HQ with (⟨%n, %si, %d', He, n, si, err, Hdst, Hsrc, src, dst, enc, %Hv, %Hinv'⟩ |
            ⟨%n, %err', %d', He, n, err, Hdst, Hsrc, %Hret⟩)
          · subst Hv
            icases base64.enc_open e enc dqe $$ He with ⟨-, Hf⟩
            icases Hf with ⟨Henc, Hdm, Hpad, Hstrict⟩
            try wp_auto
            ihave HI : (∃ (n si : w64) (d' : List w8),
                "n" ∷ n_ptr ↦ n ∗ "si" ∷ si_ptr ↦ si ∗ "err" ∷ err_ptr ↦ GoInterface.nil ∗ "Hdst" ∷ dst ↦* d' ∗
                "%Hinv'" ∷ ⌜d'.length = d.length ∧ 0 ≤ sint.Z si ∧ sint.Z si ≤ s.length ∧ 0 ≤ sint.Z n ∧
                  sint.Z n ≤ d.length ∧ ((∃ k : Nat, sint.Z n = 3 * k ∧ 4 * k ≤ sint.Z si) ∨ sint.Z si = s.length) ∧
                  (base64.decOk enc → (base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL s) ↔
                    base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si)))))⌝ : IProp GF)
                $$ [n si err Hdst]
            · iexists _, _, _; iframe; ipureintro; exact Hinv'
            wp_for HI
            by_cases hc1 : sint.Z si < sint.Z src.len
            · rw [decide_eq_true hc1]
              try wp_auto
              first | rw [base64.ite_tt] | rw [if_pos rfl]
              have hqa : 0 ≤ sint.Z si := Hinv'.2.1
              have hqb : sint.Z si ≤ s.length := Hinv'.2.2.1
              have hsp : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z dst.len := by
                have := Hinv'.2.2.2.1; have := Hinv'.2.2.2.2.1; have := Hinv'.1; constructor <;> word
              have hsl1 : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z dst.len ∧ sint.Z dst.len ≤ sint.Z dst.cap :=
                ⟨hsp.1, hsp.2, Hdw.2⟩
              have hcomb : (d'.take (sint.nat n)).length = sint.nat n := by
                simp only [List.length_take]; have := Hinv'.1; have := Hinv'.2.2.2.2.1; word
              wp_pures
              try wp_auto
              rw [ite_eq_left_of_eq_true _ _ (eq_true hsl1)]
              ihave ⟨Hd1, Hd2⟩ := base64.dst_split dst d' n hsp $$ Hdst
              ihave He : e ↦{dqe} enc $$ [Henc Hdm Hpad Hstrict]
              · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
              have hroom' : 3 * ((s.length - sint.nat si) / 4) ≤ (d'.drop (sint.nat n)).length := by
                rw [List.length_drop]
                have := Hinv'.1
                rcases Hinv'.2.2.2.2.2.1 with ⟨k, hk1, hk2⟩ | h
                · have hn' : sint.nat n = 3 * k := by word
                  have hs' : 4 * k ≤ sint.nat si := by word
                  have hsl : sint.nat si ≤ s.length := by word
                  have hdl' : d'.length = d.length := Hinv'.1
                  omega
                · have : s.length - sint.nat si = 0 := by word
                  rw [this]; omega
              try wp_auto
              wp_bind (App (App (App (Val _) (Val _)) (Val _)) (Val _))
              iapply (wp_decodeQuantum e enc dqe _ src (d'.drop (sint.nat n)) s dq si hpad hstrict hdm
                  hqa hqb hroom') $$ [He Hd2 Hsrc]
              · iframe
              inext
              iintro %si' %ninc %qerr ⟨%d2, He, Hd2, Hsrc, %Hq⟩
              obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7⟩ := Hq
              ihave Hdst := base64.dst_combine dst (d'.take (sint.nat n)) d2 n hcomb hsp $$ [Hd1 Hd2]
              · iframe
              icases base64.enc_open e enc dqe $$ He with ⟨-, Hf⟩
              icases Hf with ⟨Henc, Hdm, Hpad, Hstrict⟩
              try wp_auto
              have hlen' : (d'.take (sint.nat n) ++ d2).length = d.length := by
                rw [List.length_append, List.length_take, hq1, List.length_drop]
                have := Hinv'.1; have := Hinv'.2.2.2.2.1; word
              have hnb : sint.Z n + sint.Z ninc ≤ d.length := by
                have := Hinv'.1
                rcases Hinv'.2.2.2.2.2.1 with ⟨k, hk1, hk2⟩ | h
                · have h3 : 3 * (s.length / 4) ≤ d.length := hroom
                  have : sint.Z ninc ≤ 3 * ((sint.Z si' - sint.Z si) / 4) := hq5
                  have hsl : sint.Z si' ≤ s.length := hq3
                  omega
                · have : sint.Z si' = sint.Z si := by omega
                  have : sint.Z ninc ≤ 0 := by rw [this] at hq5; simpa using hq5
                  have := Hinv'.2.2.2.2.1; omega
              rcases qerr with qei | _
              · -- the quantum's error: returned
                try wp_auto
                wp_for_post
                try wp_auto
                iapply HΦ; iexists _
                isplitl [Henc Hdm Hpad Hstrict]
                · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
                iframe; ipureintro
                refine ⟨hlen', by word, by word, fun hok => ⟨fun h => absurd h (by intro h'; cases h'), fun hb => ?_⟩⟩
                exact absurd ((Hinv'.2.2.2.2.2.2 hok).1 hb) ((hq7 hok).2 (by intro h'; cases h'))
              · -- no error: on
                try wp_auto
                wp_for_post
                iframe; iexists n + ninc, si', _; iframe; ipureintro
                refine ⟨hlen', by word, hq3, by word, by word, ?_, fun hok => ?_⟩
                · rcases hq6 rfl with ⟨h3, h4⟩ | h
                  · rcases Hinv'.2.2.2.2.2.1 with ⟨k, hk1, hk2⟩ | h'
                    · exact .inl ⟨k + 1, by word, by word⟩
                    · exfalso; omega
                  · exact .inr h
                · exact (Hinv'.2.2.2.2.2.2 hok).trans (base64.quantumOk_iff ((hq7 hok).1 rfl))
            · -- the end: `return n, err`
              rw [decide_eq_false hc1]
              try wp_auto
              first | rw [base64.ite_ft, base64.ite_ff] | skip
              repeat (first | rw [if_neg Bool.false_ne_true] | rw [if_pos rfl])
              try wp_auto
              iapply HΦ; iexists _
              isplitl [Henc Hdm Hpad Hstrict]
              · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
              iframe; ipureintro
              have hend : s.length ≤ sint.nat si := by have := Hsl.1; have := Hinv'.2.1; word
              exact ⟨Hinv'.1, Hinv'.2.2.2.1, Hinv'.2.2.2.2.1, fun hok => ⟨fun _ => (Hinv'.2.2.2.2.2.2 hok).2
                (by rw [base64.dropNL_drop_end s _ hend]; simp [base64.b64Ok]), fun _ => rfl⟩⟩
          · obtain ⟨hv, Hret⟩ := Hret
            subst hv
            try wp_auto
            iapply HΦ
            iexists d'
            iframe
            ipureintro; exact Hret
      · obtain ⟨hv, Hret⟩ := Hret
        subst hv
        try wp_auto
        iapply HΦ
        iexists d'
        iframe
        ipureintro; exact Hret

end proof

end EtcdGrove
end Perennial
