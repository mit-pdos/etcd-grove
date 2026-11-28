/-
Proof of `Encoding.decodeQuantum` over its translated body (`encoding/base64`, go1.27.3). Lean-first
(prove-authcrypto, 2026-11-21).
-/
module

public import Spec.encoding.base64.Encoding__decodeQuantum
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

set_option maxHeartbeats 4000000 in
theorem base64.Encoding.decodeQuantum.wp_proof :
    base64.Encoding.decodeQuantum.spec (GF := GF) (hG := hG) := by
  intro e enc dqe dst src d s dq si hpad hstrict hdm hsi0 hsiL hroom
  wp_start as ⟨He, Hdst, Hsrc⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hsrc
  ihave %Hdl := ownSlice_len _ _ _ $$ Hdst
  icases base64.enc_open _ _ _ $$ He with ⟨%Hnn, Hf⟩
  icases Hf with ⟨Henc, Hdm, Hpad, Hstrict⟩
  try wp_auto
  have hp61 : enc.padChar' ≠ W32 (-1) := by rw [hpad]; decide
  have w32_ne : ∀ c : w8, c ≠ W8 61 → W32 (uint.Z c) ≠ W32 61 := by
    intro c hc61 h
    apply hc61
    have h1 : uint.Z (W32 (uint.Z c)) = uint.Z c := by have := c.isLt; word
    have h2 : uint.Z (W32 61) = 61 := by word
    rw [h, h2] at h1
    word
  ihave HI : (∃ (j si' : w64) (db : GoArray w8 4),
      "j" ∷ j_ptr ↦ j ∗ "si" ∷ si_ptr ↦ si' ∗ "dbuf" ∷ dbuf_ptr ↦ db ∗
      "%Hinv" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 4 ∧ sint.Z si + sint.Z j ≤ sint.Z si' ∧
        sint.Z si' ≤ s.length ∧
        (base64.decOk enc →
          base64.readSyms enc.encode'.arr s (sint.nat si) (sint.nat j) (sint.nat si'))⌝ : IProp GF) $$ [j si dbuf]
  · iexists W64 0, si, _; iframe; ipureintro
    refine ⟨by word, by word, by word, hsiL, fun _ => ⟨[], rfl, by simp, rfl⟩⟩
  wp_join (Q := fun v => iprop(
      (∃ (si'' dl : w64) (err'' : GoInterface) (db' : GoArray w8 4) (j' : w64),
        "He" ∷ e ↦{dqe} enc ∗ "si" ∷ si_ptr ↦ si'' ∗ "dlen" ∷ dlen_ptr ↦ dl ∗ "err" ∷ err_ptr ↦ err'' ∗
        "dbuf" ∷ dbuf_ptr ↦ db' ∗ "j" ∷ j_ptr ↦ j' ∗ "nsi" ∷ nsi_ptr ↦ zero_val w64 ∗
        "n" ∷ n_ptr ↦ zero_val w64 ∗ "Hdst" ∷ dst ↦* d ∗ "Hsrc" ∷ src ↦*{dq} s ∗
        "enc" ∷ enc_ptr ↦ e ∗ "src" ∷ src_ptr ↦ src ∗ "dst" ∷ dst_ptr ↦ dst ∗
        "%Hex" ∷ ⌜v = executeVal ∧ (dl = W64 2 ∨ dl = W64 3 ∨ dl = W64 4) ∧
          sint.Z si + 4 ≤ sint.Z si'' ∧ sint.Z si'' ≤ s.length ∧
          (err'' = GoInterface.nil → dl = W64 4 ∨ sint.Z si'' = s.length) ∧
          (base64.decOk enc →
            (err'' = GoInterface.nil → base64.quantumOk enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si)))
              (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si'')))) ∧
            (err'' ≠ GoInterface.nil → ¬ base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si)))))⌝) ∨
      (∃ (si' ninc : w64) (err : GoInterface) (d' : List w8),
        "He" ∷ e ↦{dqe} enc ∗ "nsi" ∷ nsi_ptr ↦ si' ∗ "n" ∷ n_ptr ↦ ninc ∗ "err" ∷ err_ptr ↦ err ∗
        "Hdst" ∷ dst ↦* d' ∗ "Hsrc" ∷ src ↦*{dq} s ∗
        "%Hret" ∷ ⌜v = returnVal #() ∧ d'.length = d.length ∧ sint.Z si ≤ sint.Z si' ∧
          sint.Z si' ≤ s.length ∧ 0 ≤ sint.Z ninc ∧ sint.Z ninc ≤ 3 * ((sint.Z si' - sint.Z si) / 4) ∧
          (err = GoInterface.nil →
            (sint.Z ninc = 3 ∧ sint.Z si + 4 ≤ sint.Z si') ∨ sint.Z si' = s.length) ∧
          (base64.decOk enc →
            (err = GoInterface.nil → base64.quantumOk enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si)))
              (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si')))) ∧
            (err ≠ GoInterface.nil → ¬ base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si)))))⌝))) at next
    with [-HΦ]
  · wp_for HI
    wp_if_destruct
    · have hj4 : sint.Z j < 4 := by revert Hif; word
      have hj0 := Hinv.1
      try wp_auto
      wp_if_destruct
      · -- the end of the input
        try wp_auto
        have hL : sint.Z src.len = s.length := by have := Hsl.1; word
        have hRS := Hinv.2.2.2.2
        have hle : s.length ≤ sint.nat src.len := by have := Hsl.1; word
        wp_if_destruct
        · -- `j == 0`: the end, at a quantum boundary
          try wp_auto
          wp_for_post
          iright
          iexists _, _, _, _
          isplitl [Henc Hdm Hpad Hstrict]
          · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
          iframe; ipureintro
          refine ⟨rfl, rfl, by word, by word, by word, by word, fun _ => .inr hL,
            fun hok => ⟨fun _ => ?_, fun hne => (hne rfl).elim⟩⟩
          refine base64.readSyms_end_ok (base64.readSyms_congr ?_ rfl (hRS hok)) hle
          have hj0e : j = W64 0 := by
            first | exact Hif | exact of_decide_eq_true Hif.symm | exact of_decide_eq_true Hif
          rw [hj0e]; rfl
        · try wp_auto
          simp only [hp61, decide_false, Bool.not_false, decide_true]
          try wp_auto
          wp_for_post
          iright
          iexists _, _, _, _
          isplitl [Henc Hdm Hpad Hstrict]
          · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
          iframe; ipureintro
          have hjne : ¬ j = W64 0 := by
            first | exact Hif | (intro h; apply Hif; simp [h]) | (intro h; simp [h] at Hif)
          have hjn0 : sint.Z j ≠ 0 := fun h => hjne (by word)
          refine ⟨rfl, rfl, by word, by word, by word, by word, fun h => ?_,
            fun hok => ⟨fun h => absurd h (by intro h'; cases h'), fun _ => ?_⟩⟩
          · exact absurd h (by intro h'; cases h')
          · exact base64.readSyms_end_bad (hRS hok) hle (by word) (by word)
      · have hlt : sint.Z si' < sint.Z src.len := by
          have h1 := Hinv.2.2.2.1
          have h2 : sint.Z src.len = s.length := by have := Hsl.1; word
          have h3 : si' ≠ src.len := fun h => Hif h.symm
          have : sint.Z si' ≠ sint.Z src.len := fun h => h3 (by word)
          omega
        obtain ⟨c, hc⟩ : ∃ c, s[(sint.Z si').toNat]? = some c :=
          ⟨_, List.getElem?_eq_getElem (by have := Hsl.1; word)⟩
        have hc' : s[sint.nat si']? = some c := by
          rw [show sint.nat si' = (sint.Z si').toNat by word]; exact hc
        have hsucc : sint.nat (si' + W64 1) = sint.nat si' + 1 := by
          have := Hsl.1; have := Hinv.2.2.2.1; word
        have hRS := Hinv.2.2.2.2
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, hlt⟩)]
        wp_apply wp_load_slice_index src _ s _ c (by word) $$ [Hsrc] as Hsrc
        · iframe; ipureintro; exact hc
        try wp_auto
        have hcb : 0 ≤ sint.Z (W64 (uint.Z c)) ∧ sint.Z (W64 (uint.Z c)) < 256 := by
          have := c.isLt; constructor <;> word
        rw [ite_eq_left_of_eq_true _ _ (eq_true hcb)]
        wp_apply (base64.wp_load_arr _ 256 _ dqe _ hcb) $$ Hdm as Hdm
        have hidx : (sint.Z (W64 (uint.Z c))).toNat = c.toNat := by have := c.isLt; word
        rw [hidx]
        try wp_auto
        wp_if_destruct
        · -- not a symbol
          have hnsym : base64.decOk enc → c ∉ enc.encode'.arr := fun hok hm => by
            have := base64.decOk_sym hok c hm; rw [Hif] at this; exact absurd this (by decide)
          have h2 : sint.Z src.len = s.length := by have := Hsl.1; word
          wp_if_destruct
          · -- '\n': skipped
            try wp_auto
            wp_for_post
            iframe
            iexists _, si' + W64 1, _
            iframe; ipureintro
            refine ⟨by word, by word, by word, by word, fun hok => ?_⟩
            refine base64.readSyms_congr (by word) hsucc.symm (base64.readSyms_nl (hRS hok) hc' (.inl ?_))
            first | rfl | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
          · have hn10 : c ≠ W8 10 := by
              first | exact Hif | exact fun h => Hif (by rw [h]; rfl)
            wp_if_destruct
            · -- '\r': skipped
              try wp_auto
              wp_for_post
              iframe
              iexists _, si' + W64 1, _
              iframe; ipureintro
              refine ⟨by word, by word, by word, by word, fun hok => ?_⟩
              refine base64.readSyms_congr (by word) hsucc.symm (base64.readSyms_nl (hRS hok) hc' (.inr ?_))
              first | rfl | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)

            · -- `=`, or a byte that is not base64
              have hn13 : c ≠ W8 13 := by
                first | exact Hif | exact fun h => Hif (by rw [h]; rfl)
              try wp_auto
              rw [hpad]
              by_cases hc61 : c = W8 61
              · -- `=`: the padding
                subst hc61
                simp only [show W32 (uint.Z (W8 61)) = W32 61 from rfl, _root_.decide_true, Bool.not_true]
                try wp_auto
                wp_if_destruct
                · -- `j == 1`: a padding after one symbol
                  try wp_auto
                  wp_for_post
                  iright
                  iexists _, _, _, _
                  isplitl [Henc Hdm Hpad Hstrict]
                  · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; (try rw [hpad]); iframe
                  iframe; ipureintro
                  refine ⟨rfl, rfl, by word, by word, by word, by word, fun h => absurd h (by intro h'; cases h'),
                    fun hok => ⟨fun h => absurd h (by intro h'; cases h'), fun _ => ?_⟩⟩
                  exact base64.readSyms_bad hok.2.1 (hRS hok) (by word) hc' (hnsym hok) hn10 hn13
                    (.inr (by first | word | (subst_vars; word)))
                · wp_if_destruct
                  · -- `j == 0`: a padding first
                    try wp_auto
                    wp_for_post
                    iright
                    iexists _, _, _, _
                    isplitl [Henc Hdm Hpad Hstrict]
                    · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; (try rw [hpad]); iframe
                    iframe; ipureintro
                    refine ⟨rfl, rfl, by word, by word, by word, by word, fun h => absurd h (by intro h'; cases h'),
                      fun hok => ⟨fun h => absurd h (by intro h'; cases h'), fun _ => ?_⟩⟩
                    exact base64.readSyms_bad hok.2.1 (hRS hok) (by word) hc' (hnsym hok) hn10 hn13
                      (.inr (by first | word | (subst_vars; word)))
                  · -- `j` is 2 or 3: the padding of the last quantum
                    have hj23 : sint.Z j = 2 ∨ sint.Z j = 3 := by
                      have h0 : j ≠ W64 0 := by assumption
                      have h1 : j ≠ W64 1 := by assumption
                      have := Hinv.1
                      have h0' : sint.Z j ≠ 0 := fun h => h0 (by word)
                      have h1' : sint.Z j ≠ 1 := fun h => h1 (by word)
                      omega
                    have hP := fun hok => base64.readSyms_pad (hRS hok) hc'
                    wp_if_destruct
                    · -- `j == 2`: a second `=` expected
                      ihave HA : (∃ x : w64, "si" ∷ si_ptr ↦ x ∗
                          "%Hx" ∷ ⌜sint.Z si' + 1 ≤ sint.Z x ∧ sint.Z x ≤ s.length ∧
                            _root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si' + 1)) = _root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat x))⌝ : IProp GF) $$ [si]
                      · iexists _; iframe; ipureintro
                        refine ⟨by word, by word, by rw [hsucc]⟩
                      wp_for HA
                      wp_if_destruct
                      · -- `si < len(src)`: is `src[si]` a newline?
                        obtain ⟨y, hy⟩ : ∃ y, s[(sint.Z x).toNat]? = some y :=
                          ⟨_, List.getElem?_eq_getElem (by have := Hsl.1; word)⟩
                        have hy' : s[sint.nat x]? = some y := by
                          rw [show sint.nat x = (sint.Z x).toNat by word]; exact hy
                        have hxs : sint.nat (x + W64 1) = sint.nat x + 1 := by
                          have := Hsl.1; have := Hx.2.1; word
                        have hX := Hx.2.2
                        try wp_auto
                        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
                        wp_apply wp_load_slice_index src _ s _ y (by word) $$ [Hsrc] as Hsrc
                        · iframe; ipureintro; exact hy
                        try wp_auto
                        wp_if_destruct
                        · -- '\n': skipped
                          try wp_auto
                          wp_for_post
                          iframe; iexists _; iframe; ipureintro
                          refine ⟨by word, by word, ?_⟩
                          rw [hX, base64.dropNL_drop_skip s _ _ hy' (.inl ?_), hxs]
                          first | rfl | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
                        · have hn10y : y ≠ W8 10 := by
                            first | exact Hif | exact fun h => Hif (by rw [h]; rfl)
                          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
                          wp_apply wp_load_slice_index src _ s _ y (by word) $$ [Hsrc] as Hsrc
                          · iframe; ipureintro; exact hy
                          try wp_auto
                          wp_if_destruct
                          · -- '\r': skipped
                            try wp_auto
                            wp_for_post
                            iframe; iexists _; iframe; ipureintro
                            refine ⟨by word, by word, ?_⟩
                            rw [hX, base64.dropNL_drop_skip s _ _ hy' (.inr ?_), hxs]
                            first | rfl | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
                          · -- the loop ends at a byte other than a newline: is it `=`?
                            have hy13 : ¬ y = W8 13 := fun h => Hif (by rw [h]; rfl)
                            simp only [hy13, decide_false, Bool.false_eq_true, ↓reduceIte]
                            try wp_auto
                            wp_if_destruct
                            · exfalso; omega
                            · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
                              wp_apply wp_load_slice_index src _ s _ y (by word) $$ [Hsrc] as Hsrc
                              · iframe; ipureintro; exact hy
                              try wp_auto
                              by_cases hy61' : y = W8 61
                              · subst hy61'
                                simp only [show W32 (uint.Z (W8 61)) = W32 61 from rfl, _root_.decide_true, Bool.not_true]
                                try wp_auto
                                have hP2 : base64.decOk enc → ∃ pre : List w8, pre.length = 2 ∧
                                    (∀ z ∈ pre, z ∈ enc.encode'.arr) ∧
                                    _root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si)) = pre ++ 61 :: 61 :: _root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat x + 1)) := by
                                  intro hok
                                  obtain ⟨pre, hl, hp, he⟩ := hP hok
                                  refine ⟨pre, by rw [hl]; word, hp, ?_⟩
                                  rw [he, hX, base64.dropNL_drop_keep s _ _ hy' (by decide) (by decide)]; rfl
                                have hz : sint.Z si + 4 ≤ sint.Z (x + W64 1) ∧ sint.Z (x + W64 1) ≤ s.length ∧
                                    _root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat x + 1)) = _root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat (x + W64 1))) := by
                                  have := Hx.2.1
                                  refine ⟨by have := Hinv.2.2.1; have := Hx.1; word, by have := Hsl.1; word, by rw [hxs]⟩
                                ihave HB : (∃ w : w64, "si" ∷ si_ptr ↦ w ∗ "%Hw" ∷ ⌜sint.Z si + 4 ≤ sint.Z w ∧ sint.Z w ≤ s.length ∧
                                    _root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat x + 1)) = _root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat w))⌝ : IProp GF) $$ [si]
                                · iexists _; iframe; ipureintro; exact hz
                                wp_for HB
                                wp_if_destruct
                                · -- a byte left: a newline is skipped, anything else is trailing garbage
                                  obtain ⟨y2, hy2⟩ : ∃ y, s[(sint.Z w).toNat]? = some y :=
                                    ⟨_, List.getElem?_eq_getElem (by have := Hsl.1; word)⟩
                                  have hy2' : s[sint.nat w]? = some y2 := by
                                    rw [show sint.nat w = (sint.Z w).toNat by word]; exact hy2
                                  have hws : sint.nat (w + W64 1) = sint.nat w + 1 := by
                                    have := Hsl.1; have := Hw.2.1; word
                                  have hW := Hw.2.2
                                  try wp_auto
                                  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
                                  wp_apply wp_load_slice_index src _ s _ y2 (by word) $$ [Hsrc] as Hsrc
                                  · iframe; ipureintro; exact hy2
                                  try wp_auto
                                  wp_if_destruct
                                  · try wp_auto
                                    wp_for_post
                                    iframe; iexists _; iframe; ipureintro
                                    refine ⟨by word, by word, ?_⟩
                                    rw [hW, base64.dropNL_drop_skip s _ _ hy2' (.inl ?_), hws]
                                    first | rfl | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
                                  · have hn10z : y2 ≠ W8 10 := by
                                      first | exact Hif | exact fun h => Hif (by rw [h]; rfl)
                                    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
                                    wp_apply wp_load_slice_index src _ s _ y2 (by word) $$ [Hsrc] as Hsrc
                                    · iframe; ipureintro; exact hy2
                                    try wp_auto
                                    wp_if_destruct
                                    · try wp_auto
                                      wp_for_post
                                      iframe; iexists _; iframe; ipureintro
                                      refine ⟨by word, by word, ?_⟩
                                      rw [hW, base64.dropNL_drop_skip s _ _ hy2' (.inr ?_), hws]
                                      first | rfl | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
                                    · have hy13 : ¬ y2 = W8 13 := fun h => Hif (by rw [h]; rfl)
                                      simp only [hy13, decide_false, Bool.false_eq_true, ↓reduceIte]
                                      try wp_auto
                                      wp_if_destruct
                                      · try wp_auto
                                        wp_for_post
                                        ileft; iexists w, _, _, db, _
                                        isplitl [Henc Hdm Hpad Hstrict]
                                        · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; (try rw [hpad]); iframe
                                        iframe; ipureintro
                                        refine ⟨rfl, .inl rfl, Hw.1, Hw.2.1, fun h => absurd h (by intro h'; cases h'),
                                          fun hok => ⟨fun h => absurd h (by intro h'; cases h'), fun _ => ?_⟩⟩
                                        obtain ⟨pre, hl, hp, he⟩ := hP2 hok
                                        rw [he, hW, base64.dropNL_drop_keep s _ _ hy2' hn10z hy13]
                                        exact base64.pad2_bad _ hok.2.1 pre _ hp hl (by simp)
                                      · exfalso; omega
                                · -- the end of the input
                                  have hwL : sint.Z w = s.length := by
                                    have : ¬ sint.Z w < sint.Z src.len := by assumption
                                    have := Hw.2.1; have := Hsl.1; word
                                  have hwe : s.length ≤ sint.nat w := by word
                                  try wp_auto
                                  wp_if_destruct
                                  · exfalso; have := Hsl.1; word
                                  · try wp_auto
                                    wp_for_post
                                    ileft; iexists w, _, _, db, _
                                    isplitl [Henc Hdm Hpad Hstrict]
                                    · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; (try rw [hpad]); iframe
                                    iframe; ipureintro
                                    refine ⟨rfl, .inl rfl, Hw.1, Hw.2.1, fun _ => .inr hwL,
                                      fun hok => ⟨fun _ => ?_, fun hne => (hne rfl).elim⟩⟩
                                    obtain ⟨pre, hl, hp, he⟩ := hP2 hok
                                    refine .inl ⟨base64.dropNL_drop_end s _ hwe, ?_⟩
                                    rw [he, Hw.2.2, base64.dropNL_drop_end s _ hwe]
                                    exact base64.b64Ok_pad2 _ pre hp hl
                              · rw [decide_eq_false (w32_ne y hy61'), Bool.not_false]
                                try wp_auto
                                wp_for_post
                                iright
                                iexists _, _, _, _
                                isplitl [Henc Hdm Hpad Hstrict]
                                · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; (try rw [hpad]); iframe
                                iframe; ipureintro
                                refine ⟨rfl, rfl, by word, by word, by word, by word, fun h => absurd h (by intro h'; cases h'),
                                  fun hok => ⟨fun h => absurd h (by intro h'; cases h'), fun _ => ?_⟩⟩
                                obtain ⟨pre, hl, hp, he⟩ := hP hok
                                rw [he, hX, base64.dropNL_drop_keep s _ _ hy' hn10y hy13]
                                exact base64.pad2_bad _ hok.2.1 pre _ hp (by rw [hl]; word)
                                  (fun h => hy61' (List.cons.inj h).1)
                      · -- the end of the input: not enough padding
                        have hxL : sint.Z x = s.length := by
                          have h3 := Hx.2.1
                          have : ¬ sint.Z x < sint.Z src.len := by assumption
                          omega
                        have hxe : s.length ≤ sint.nat x := by word
                        try wp_auto
                        wp_if_destruct
                        · try wp_auto
                          wp_for_post
                          iright
                          iexists _, _, _, _
                          isplitl [Henc Hdm Hpad Hstrict]
                          · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; (try rw [hpad]); iframe
                          iframe; ipureintro
                          refine ⟨rfl, rfl, by word, by word, by word, by word, fun h => absurd h (by intro h'; cases h'),
                            fun hok => ⟨fun h => absurd h (by intro h'; cases h'), fun _ => ?_⟩⟩
                          obtain ⟨pre, hl, hp, he⟩ := hP hok
                          rw [he, Hx.2.2, base64.dropNL_drop_end s _ hxe]
                          exact base64.pad2_bad _ hok.2.1 pre _ hp (by rw [hl]; word) (by simp)
                        · exfalso; apply Hif; word
                    · -- `j == 3`: the quantum ends
                      have hj3 : j = W64 3 := by
                        have : j ≠ W64 2 := by assumption
                        rcases hj23 with h | h
                        · exact absurd (by word) this
                        · word
                      subst hj3
                      try wp_auto
                      have hz : sint.Z si + 4 ≤ sint.Z (si' + W64 1) ∧ sint.Z (si' + W64 1) ≤ s.length ∧
                          _root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si' + 1)) = _root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat (si' + W64 1))) := by
                        refine ⟨by have := Hinv.2.2.1; word, by have := Hsl.1; word, by rw [hsucc]⟩
                      ihave HB : (∃ w : w64, "si" ∷ si_ptr ↦ w ∗ "%Hw" ∷ ⌜sint.Z si + 4 ≤ sint.Z w ∧ sint.Z w ≤ s.length ∧
                          _root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si' + 1)) = _root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat w))⌝ : IProp GF) $$ [si]
                      · iexists _; iframe; ipureintro; exact hz
                      wp_for HB
                      wp_if_destruct
                      · -- a byte left: a newline is skipped, anything else is trailing garbage
                        obtain ⟨y2, hy2⟩ : ∃ y, s[(sint.Z w).toNat]? = some y :=
                          ⟨_, List.getElem?_eq_getElem (by have := Hsl.1; word)⟩
                        have hy2' : s[sint.nat w]? = some y2 := by
                          rw [show sint.nat w = (sint.Z w).toNat by word]; exact hy2
                        have hws : sint.nat (w + W64 1) = sint.nat w + 1 := by
                          have := Hsl.1; have := Hw.2.1; word
                        have hW := Hw.2.2
                        try wp_auto
                        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
                        wp_apply wp_load_slice_index src _ s _ y2 (by word) $$ [Hsrc] as Hsrc
                        · iframe; ipureintro; exact hy2
                        try wp_auto
                        wp_if_destruct
                        · try wp_auto
                          wp_for_post
                          iframe; iexists _; iframe; ipureintro
                          refine ⟨by word, by word, ?_⟩
                          rw [hW, base64.dropNL_drop_skip s _ _ hy2' (.inl ?_), hws]
                          first | rfl | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
                        · have hn10z : y2 ≠ W8 10 := by
                            first | exact Hif | exact fun h => Hif (by rw [h]; rfl)
                          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
                          wp_apply wp_load_slice_index src _ s _ y2 (by word) $$ [Hsrc] as Hsrc
                          · iframe; ipureintro; exact hy2
                          try wp_auto
                          wp_if_destruct
                          · try wp_auto
                            wp_for_post
                            iframe; iexists _; iframe; ipureintro
                            refine ⟨by word, by word, ?_⟩
                            rw [hW, base64.dropNL_drop_skip s _ _ hy2' (.inr ?_), hws]
                            first | rfl | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
                          · have hy13 : ¬ y2 = W8 13 := fun h => Hif (by rw [h]; rfl)
                            simp only [hy13, decide_false, Bool.false_eq_true, ↓reduceIte]
                            try wp_auto
                            wp_if_destruct
                            · try wp_auto
                              wp_for_post
                              ileft; iexists w, _, _, db, _
                              isplitl [Henc Hdm Hpad Hstrict]
                              · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; (try rw [hpad]); iframe
                              iframe; ipureintro
                              refine ⟨rfl, .inr (.inl rfl), Hw.1, Hw.2.1, fun h => absurd h (by intro h'; cases h'),
                                fun hok => ⟨fun h => absurd h (by intro h'; cases h'), fun _ => ?_⟩⟩
                              obtain ⟨pre, hl, hp, he⟩ := hP hok
                              rw [he, hW, base64.dropNL_drop_keep s _ _ hy2' hn10z hy13]
                              exact base64.pad3_bad _ hok.2.1 pre _ hp (by rw [hl]; word) (by simp)
                            · exfalso; omega
                      · -- the end of the input
                        have hwL : sint.Z w = s.length := by
                          have : ¬ sint.Z w < sint.Z src.len := by assumption
                          have := Hw.2.1; have := Hsl.1; word
                        have hwe : s.length ≤ sint.nat w := by word
                        try wp_auto
                        wp_if_destruct
                        · exfalso; have := Hsl.1; word
                        · try wp_auto
                          wp_for_post
                          ileft; iexists w, _, _, db, _
                          isplitl [Henc Hdm Hpad Hstrict]
                          · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; (try rw [hpad]); iframe
                          iframe; ipureintro
                          refine ⟨rfl, .inr (.inl rfl), Hw.1, Hw.2.1, fun _ => .inr hwL,
                            fun hok => ⟨fun _ => ?_, fun hne => (hne rfl).elim⟩⟩
                          obtain ⟨pre, hl, hp, he⟩ := hP hok
                          refine .inl ⟨base64.dropNL_drop_end s _ hwe, ?_⟩
                          rw [he, Hw.2.2, base64.dropNL_drop_end s _ hwe]
                          exact base64.b64Ok_pad1 _ pre hp (by rw [hl]; word)
              · -- not base64
                have hne : W32 (uint.Z c) ≠ W32 61 := by
                  intro h
                  apply hc61
                  have h1 : uint.Z (W32 (uint.Z c)) = uint.Z c := by have := c.isLt; word
                  have h2 : uint.Z (W32 61) = 61 := by word
                  rw [h, h2] at h1
                  word
                rw [decide_eq_false hne, Bool.not_false]
                try wp_auto
                wp_for_post
                iright
                iexists _, _, _, _
                isplitl [Henc Hdm Hpad Hstrict]
                · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; (try rw [hpad]); iframe
                iframe; ipureintro
                refine ⟨rfl, rfl, by word, by word, by word, by word, fun h => absurd h (by intro h'; cases h'),
                  fun hok => ⟨fun h => absurd h (by intro h'; cases h'), fun _ => ?_⟩⟩
                exact base64.readSyms_bad hok.2.1 (hRS hok) (by word) hc' (hnsym hok) hn10 hn13 (.inl hc61)
        · -- a symbol: `dbuf[j] = out`, next symbol
          have hsym : base64.decOk enc → c ∈ enc.encode'.arr := fun hok =>
            base64.decOk_sym_of_ne hok c (by first | exact Hif | exact fun h => Hif h | simpa using Hif)
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hinv.1, hj4⟩)]
          wp_apply (base64.wp_store_arr _ 4 _ _ _ ⟨Hinv.1, hj4⟩) $$ dbuf as dbuf
          try wp_auto
          wp_for_post
          iframe
          iexists j + W64 1, si' + W64 1, _
          iframe; ipureintro
          have h2 : sint.Z src.len = s.length := by have := Hsl.1; word
          refine ⟨by word, by word, by word, by word, fun hok => ?_⟩
          exact base64.readSyms_congr (by word) hsucc.symm
            (base64.readSyms_sym (hRS hok) hc' (hsym hok) (base64.decOk_ne10 hok (hsym hok))
              (base64.decOk_ne13 hok (hsym hok)))

    · -- four symbols read
      have hj : sint.Z j = 4 := by
        have := Hinv.2.1; have : ¬ sint.Z j < sint.Z (W64 4) := by assumption
        word
      ileft; iexists si', _, _, db, j
      isplitl [Henc Hdm Hpad Hstrict]
      · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; iframe
      iframe; ipureintro
      refine ⟨trivial, .inr (.inr rfl), by have := Hinv.2.2.1; word, Hinv.2.2.2.1, fun _ => .inl rfl,
        fun hok => ⟨fun _ => base64.readSyms_four (base64.readSyms_congr (by word) rfl (Hinv.2.2.2.2 hok)),
          fun hne => (hne rfl).elim⟩⟩

  · iintro HQ
    icases HQ with (⟨%si'', %dl, %err'', %db', %j', He, si, dlen, err, dbuf, j, nsi, n, Hdst, Hsrc, enc, src, dst, %Hex⟩ |
      ⟨%si', %ninc, %err', %d', He, nsi, n, err, Hdst, Hsrc, %Hret⟩)
    · obtain ⟨rfl, Hex⟩ := Hex
      icases base64.enc_open e enc dqe $$ He with ⟨%Hnn', Hf⟩
      icases Hf with ⟨Henc, Hdm, Hpad, Hstrict⟩
      rw [hstrict]
      have hd3 : 3 ≤ d.length := by
        have := Hex.2.1; have := Hex.2.2.1; have := Hsl.1
        have : 4 ≤ s.length - sint.nat si := by word
        have : 1 ≤ (s.length - sint.nat si) / 4 := by omega
        omega
      have hdl := Hdl.1
      try wp_auto
      try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply (base64.wp_load_arr dbuf_ptr 4 _ _ (sint.Z (W64 0)) ⟨by word, by word⟩) $$ dbuf as dbuf
      try wp_auto
      try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply (base64.wp_load_arr dbuf_ptr 4 _ _ (sint.Z (W64 1)) ⟨by word, by word⟩) $$ dbuf as dbuf
      try wp_auto
      try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply (base64.wp_load_arr dbuf_ptr 4 _ _ (sint.Z (W64 2)) ⟨by word, by word⟩) $$ dbuf as dbuf
      try wp_auto
      try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply (base64.wp_load_arr dbuf_ptr 4 _ _ (sint.Z (W64 3)) ⟨by word, by word⟩) $$ dbuf as dbuf
      try wp_auto
      try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply (base64.wp_store_arr dbuf_ptr 4 _ (sint.Z (W64 2)) _ ⟨by word, by word⟩) $$ dbuf as dbuf
      try wp_auto
      try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply (base64.wp_store_arr dbuf_ptr 4 _ (sint.Z (W64 1)) _ ⟨by word, by word⟩) $$ dbuf as dbuf
      try wp_auto
      try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply (base64.wp_store_arr dbuf_ptr 4 _ (sint.Z (W64 0)) _ ⟨by word, by word⟩) $$ dbuf as dbuf
      try wp_auto
      rcases Hex.1 with hdl4 | hdl4 | hdl4 <;> subst hdl4
      · -- `dlen` 2
        try wp_auto
        try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (base64.wp_load_arr dbuf_ptr 4 _ _ (sint.Z (W64 0)) ⟨by word, by word⟩) $$ dbuf as dbuf
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (wp_store_slice_index dst (sint.Z (W64 0)) _ _) $$ [Hdst] as Hdst
        · iframe; ipureintro; constructor <;> (try simp only [List.length_set]) <;> word
        try wp_auto
        iapply HΦ
        iexists _
        isplitl [Henc Hdm Hpad Hstrict]
        · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; rw [hstrict]; iframe
        iframe; ipureintro
        obtain ⟨-, h4, hL, herr, hv⟩ := Hex
        refine ⟨by simp only [List.length_set], by word, hL, by word, by word, fun h => ?_, hv⟩
        · rcases herr h with h' | h'
          · exact absurd h' (by decide)
          · exact .inr h'
      · -- `dlen` 3
        try wp_auto
        try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (base64.wp_load_arr dbuf_ptr 4 _ _ (sint.Z (W64 1)) ⟨by word, by word⟩) $$ dbuf as dbuf
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (wp_store_slice_index dst (sint.Z (W64 1)) _ _) $$ [Hdst] as Hdst
        · iframe; ipureintro; constructor <;> (try simp only [List.length_set]) <;> word
        try wp_auto
        try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (base64.wp_store_arr dbuf_ptr 4 _ (sint.Z (W64 1)) _ ⟨by word, by word⟩) $$ dbuf as dbuf
        try wp_auto
        try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (base64.wp_load_arr dbuf_ptr 4 _ _ (sint.Z (W64 0)) ⟨by word, by word⟩) $$ dbuf as dbuf
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (wp_store_slice_index dst (sint.Z (W64 0)) _ _) $$ [Hdst] as Hdst
        · iframe; ipureintro; constructor <;> (try simp only [List.length_set]) <;> word
        try wp_auto
        iapply HΦ
        iexists _
        isplitl [Henc Hdm Hpad Hstrict]
        · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; rw [hstrict]; iframe
        iframe; ipureintro
        obtain ⟨-, h4, hL, herr, hv⟩ := Hex
        refine ⟨by simp only [List.length_set], by word, hL, by word, by word, fun h => ?_, hv⟩
        · rcases herr h with h' | h'
          · exact absurd h' (by decide)
          · exact .inr h'
      · -- `dlen` 4
        try wp_auto
        try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (base64.wp_load_arr dbuf_ptr 4 _ _ (sint.Z (W64 2)) ⟨by word, by word⟩) $$ dbuf as dbuf
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (wp_store_slice_index dst (sint.Z (W64 2)) _ _) $$ [Hdst] as Hdst
        · iframe; ipureintro; constructor <;> (try simp only [List.length_set]) <;> word
        try wp_auto
        try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (base64.wp_store_arr dbuf_ptr 4 _ (sint.Z (W64 2)) _ ⟨by word, by word⟩) $$ dbuf as dbuf
        try wp_auto
        try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (base64.wp_load_arr dbuf_ptr 4 _ _ (sint.Z (W64 1)) ⟨by word, by word⟩) $$ dbuf as dbuf
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (wp_store_slice_index dst (sint.Z (W64 1)) _ _) $$ [Hdst] as Hdst
        · iframe; ipureintro; constructor <;> (try simp only [List.length_set]) <;> word
        try wp_auto
        try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (base64.wp_store_arr dbuf_ptr 4 _ (sint.Z (W64 1)) _ ⟨by word, by word⟩) $$ dbuf as dbuf
        try wp_auto
        try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (base64.wp_load_arr dbuf_ptr 4 _ _ (sint.Z (W64 0)) ⟨by word, by word⟩) $$ dbuf as dbuf
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply (wp_store_slice_index dst (sint.Z (W64 0)) _ _) $$ [Hdst] as Hdst
        · iframe; ipureintro; constructor <;> (try simp only [List.length_set]) <;> word
        try wp_auto
        iapply HΦ
        iexists _
        isplitl [Henc Hdm Hpad Hstrict]
        · iapply base64.enc_close e enc dqe Hnn; unfold base64.encFields; rw [hstrict]; iframe
        iframe; ipureintro
        obtain ⟨-, h4, hL, herr, hv⟩ := Hex
        refine ⟨by simp only [List.length_set], by word, hL, by word, by word, fun h => ?_, hv⟩
        · rcases herr h with h' | h'
          · exact .inl ⟨by word, by word⟩
          · exact .inr h'
    · obtain ⟨rfl, Hret⟩ := Hret
      try wp_auto
      iapply HΦ
      iexists d'
      iframe
      ipureintro; exact Hret

end proof

end EtcdGrove
end Perennial
