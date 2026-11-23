/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/Decode.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
kit.go's `decode`: on a configuration message `c.encodeC cs` (nine bytes, `c` valid, `cs` changes
`decode` accepts), the configuration's struct, the changes' slice and `true`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## The message's bytes -/

theorem encodeC_head (c : Conf) (cs : List Change) :
    (c.encodeC cs)[0]? = some (W8 c.n) ∧ (c.encodeC cs)[1]? = some (W8 c.fastRead) ∧
    (c.encodeC cs)[2]? = some (W8 c.pool) ∧ (c.encodeC cs)[3]? = some (W8 c.desc) ∧
    (c.encodeC cs)[4]? = some (W8 cs.length) := by
  simp [Conf.encodeC]

theorem encodeC_change (c : Conf) (cs : List Change) (i : Nat) (ch : Change)
    (h : cs[i]? = some ch) (hl : cs.length ≤ maxChanges) :
    (c.encodeC cs)[5 + 2 * i]? = some (W8 ch.node) ∧
    (c.encodeC cs)[6 + 2 * i]? = some (W8 ch.after) := by
  unfold maxChanges at hl
  match cs, i, h with
  | [a], 0, h | [a, b], 0, h | [a, b], 1, h =>
    simp at h; subst h
    simp [Conf.encodeC, maxChanges, List.range_succ]
  | [], _, h | [a], _ + 1, h | [a, b], _ + 2, h => simp at h
  | _ :: _ :: _ :: _, _, _ => simp at hl

theorem Change.valid_lt {c : Conf} {ch : Change} (hc : c.valid) (h : ch.valid c) :
    ch.node < 7 ∧ ch.after < 8 := by
  obtain ⟨h1, -, -, -⟩ := hc
  obtain ⟨-, h2, -, h3⟩ := h
  omega

theorem W64_W8 (n : Nat) (h : n < 256) : W64 (uint.Z (W8 (n : Int))) = W64 (n : Int) := by
  word

theorem conds_ok {c : Conf} (hc : c.valid) :
    (W64 (c.n : Int) = W64 3 ∨ W64 (c.n : Int) = W64 5) ∧
    uint.Z (W64 (c.fastRead : Int)) ≤ uint.Z (W64 1) ∧ uint.Z (W64 (c.pool : Int)) ≤ uint.Z (W64 2) ∧
    (W64 (c.desc : Int) = W64 0 ∨ W64 (c.desc : Int) = W64 2 ∨ W64 (c.desc : Int) = W64 100) := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  refine ⟨?_, by word, by word, ?_⟩
  · rcases h1 with h | h <;> rw [h] <;> simp
  · rcases h4 with h | h | h <;> rw [h] <;> simp

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [SwiftNetPkgState GF] [examples.swiftnet.Assumptions]

set_option goose.wp.extras true

/-- `decode(b)` on a configuration message: the configuration, its changes, `true`. -/
theorem wp_decode (s : GoSlice) (dq : DFrac) (c : Conf) (cs : List Change) (hc : c.valid)
    (hcs : c.changesOk cs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
        s ↦*{dq} c.encodeC cs }}
      (App (Val (@! examples.swiftnet.decode)) (Val #s))
    {{ (sl : GoSlice), RET (PairV (PairV #(goConf c) #sl) #true);
        s ↦*{dq} c.encodeC cs ∗ sl ↦* cs.map goChange }} := by
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  have hs : sint.Z s.len = 9 := by
    have h1 := Hlen.1
    rw [Conf.encodeC_length] at h1
    unfold confLen maxChanges at h1
    word
  obtain ⟨h0, h1, h2, h3, h4⟩ := encodeC_head c cs
  have hlt := Conf.valid_lt hc
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hs]; decide⟩)]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) _ dq _ (by decide) $$ [$Hs] as Hs
  · ipureintro; exact h0
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hs]; decide⟩)]
  wp_apply wp_load_slice_index s (sint.Z (W64 1)) _ dq _ (by decide) $$ [$Hs] as Hs
  · ipureintro; exact h1
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hs]; decide⟩)]
  wp_apply wp_load_slice_index s (sint.Z (W64 2)) _ dq _ (by decide) $$ [$Hs] as Hs
  · ipureintro; exact h2
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hs]; decide⟩)]
  wp_apply wp_load_slice_index s (sint.Z (W64 3)) _ dq _ (by decide) $$ [$Hs] as Hs
  · ipureintro; exact h3
  rw [W64_W8 c.n hlt.1, W64_W8 c.fastRead hlt.2.1, W64_W8 c.pool hlt.2.2.1,
    W64_W8 c.desc hlt.2.2.2]
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #true⌝ ∗ c_ptr ↦ goConf c ∗ b_ptr ↦ s ∗
    s ↦*{dq} c.encodeC cs))) $$ [c b Hs]
  · have hcd := conds_ok hc
    repeat' wp_if_destruct
    all_goals first
      | (exfalso; obtain ⟨hn, hf, hp, hd⟩ := hcd
         first
           | contradiction
           | (rcases hn with h | h <;> simp_all; done)
           | (rcases hd with h | h | h <;> simp_all; done))
      | (rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hs]; decide⟩)]
         wp_apply wp_load_slice_index s (sint.Z (W64 4)) _ dq _ (by decide) $$ [$Hs] as Hs
         · ipureintro; exact h4
         iframe
         ipureintro
         have hl := hcs.1
         unfold maxChanges at hl
         rw [W64_W8 cs.length (by omega)]
         congr 2
         simp only [decide_eq_true_eq]
         word)
  iintro %v ⟨%hv, c, b, Hs⟩
  subst hv
  wp_auto
  have hl' : cs.length < 256 := by have := hcs.1; unfold maxChanges at this; omega
  ihave Hnil := ownSlice_nil (V := examples.swiftnet.change) (GF := GF) (DFrac.own 1)
  ihave Hcap := ownSliceCap_nil (V := examples.swiftnet.change) (GF := GF)
  ihave HI : (∃ (i : w64) (sl : GoSlice), "i" ∷ i_ptr ↦ i ∗ "cs" ∷ cs_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* (cs.take (uint.nat i)).map goChange ∗
      "Hcap" ∷ ownSliceCap examples.swiftnet.change sl (DFrac.own 1) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ cs.length⌝ : IProp GF) $$ [i cs Hnil Hcap]
  · rw [show (zero_val GoSlice) = slice.nil from rfl]
    iexists W64 0, slice.nil
    simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil]
    iframe
    isplitl []
    · iexact Hnil
    isplitl []
    · iexact Hcap
    ipureintro; omega
  wp_for HI
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hs]; decide⟩)]
  wp_apply wp_load_slice_index s (sint.Z (W64 4)) _ dq _ (by decide) $$ [$Hs] as Hs
  · ipureintro; exact h4
  rw [W64_W8 cs.length hl']
  wp_if_destruct
  · have Hif' := go.intoVal_inj Hif
    simp only [decide_eq_true_eq] at Hif'
    have hil : uint.nat i < cs.length := by word
    obtain ⟨ch, hch⟩ : ∃ ch, cs[uint.nat i]? = some ch :=
      Option.isSome_iff_exists.mp (by simp [hil])
    obtain ⟨hn5, hn6⟩ := encodeC_change c cs (uint.nat i) ch hch hcs.1
    have hv := hcs.2 ch (List.mem_of_getElem? hch)
    have hlt2 := Change.valid_lt hc hv
    have hi1 : uint.nat i ≤ 1 := by have := hcs.1; unfold maxChanges at this; omega
    have e5 : sint.Z (W64 5 + W64 2 * i) = ((5 + 2 * uint.nat i : Nat) : Int) := by word
    have e6 : sint.Z (W64 6 + W64 2 * i) = ((6 + 2 * uint.nat i : Nat) : Int) := by word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [e5]; omega, by rw [e5, hs]; omega⟩)]
    wp_apply wp_load_slice_index s (sint.Z (W64 5 + W64 2 * i)) _ dq _ (by rw [e5]; omega)
      $$ [$Hs] as Hs
    · ipureintro; rw [e5, Int.toNat_natCast]; exact hn5
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [e6]; omega, by rw [e6, hs]; omega⟩)]
    wp_apply wp_load_slice_index s (sint.Z (W64 6 + W64 2 * i)) _ dq _ (by rw [e6]; omega)
      $$ [$Hs] as Hs
    · ipureintro; rw [e6, Int.toNat_natCast]; exact hn6
    rw [W64_W8 _ (by omega), W64_W8 _ (by omega)]
    obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
    have hcn := hlt.1
    wp_bind (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #false⌝ ∗ c_ptr ↦ goConf c ∗
      ch_ptr ↦ goChange ch))) $$ [c ch]
    · repeat' wp_if_destruct
      all_goals (try (exfalso; word; done))
      all_goals (isplitl []; · itrivial
                 iframe c; unfold goChange; iexact ch)
    iintro %v ⟨%hv, c, ch⟩
    subst hv
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType examples.swiftnet.change.ty))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := examples.swiftnet.change) (t := examples.swiftnet.change.ty)
      [goChange ch]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hsl Hcap Hlsl] as %nsl ⟨Hsl, Hcap, -⟩
    · iframe
    wp_for_post
    iframe
    iexists i + W64 1, nsl
    have hsucc : uint.nat (i + W64 1) = uint.nat i + 1 := by word
    rw [hsucc, List.take_add_one, hch]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
    iframe
    ipureintro; omega
  · have hd : decide (uint.Z i < uint.Z (W64 ↑cs.length)) = false := by
      cases h : decide (uint.Z i < uint.Z (W64 ↑cs.length))
      · rfl
      · exact absurd (by rw [h]) Hif
    simp only [hd]
    rw [if_neg (by decide)]
    wp_auto
    have hie : uint.nat i = cs.length := by
      have : ¬ uint.Z i < uint.Z (W64 ↑cs.length) := by simpa using hd
      word
    rw [hie, List.take_length]
    iapply HΦ
    iframe

end proof

end Perennial.github_com.imdea_software.swiftpaxos
