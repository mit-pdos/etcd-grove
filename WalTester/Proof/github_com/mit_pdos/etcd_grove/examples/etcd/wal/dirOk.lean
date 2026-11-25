/- Lean-first (no Rocq counterpart). The proof of `dirOk`: the loop's state `(ok, n, dots)` is the scan
(`tStep`) of the bytes after the leading `/` read so far (`DirOk.lean`). -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.dirOk
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.compOk

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal _root_.Perennial.EtcdGrove.path

section pure

/-- One more byte of the scan. -/
theorem tScan_take_succ (p : GoString) (j : Nat) (b : w8) (hb : p[j + 1]? = some b)
    (s0 : Bool × Nat × Bool) :
    ((p.drop 1).take (j + 1)).foldl tStep s0 = tStep (((p.drop 1).take j).foldl tStep s0) b := by
  have hb' : (p.drop 1)[j]? = some b := by rw [List.getElem?_drop]; rwa [Nat.add_comm]
  rw [List.take_succ, hb', List.foldl_append]
  rfl

/-- The scan's length bound. -/
theorem tScan_n_le (q : List w8) (s0 : Bool × Nat × Bool) :
    (q.foldl tStep s0).2.1 ≤ s0.2.1 + q.length := by
  induction q generalizing s0 with
  | nil => simp
  | cons c q ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (tStep s0 c)
    unfold tStep at this ⊢
    split at this <;> simp_all <;> omega

/-- The end of the scan: `dirOk`'s result `true` means `tDirOk p`. -/
theorem tDirOk_of_end (p : GoString) (j : Nat) (hj : j + 1 = p.length) (hlt : p.length < 4000)
    (h0 : p[0]? = some slash) (okv : Bool) (nn : Nat) (dv : Bool)
    (hf : ((p.drop 1).take j).foldl tStep (true, 0, true) = (okv, nn, dv))
    (hres : (okv && tCompOk nn dv) = true) : tDirOk p := by
  have ht : (p.drop 1).take j = p.drop 1 := List.take_of_length_le (by simp; omega)
  rw [ht] at hf
  exact tDirOk_of_scan p hlt h0 (by rw [hf]; exact hres)

/-- A `/`: the component ends. -/
theorem tScan_slash (p : GoString) (j : Nat) (hc : p[j + 1]? = some (W8 47)) (okv : Bool) (nn : Nat)
    (dv : Bool) (hf : ((p.drop 1).take j).foldl tStep (true, 0, true) = (okv, nn, dv)) :
    ((p.drop 1).take (j + 1)).foldl tStep (true, 0, true) = (okv && tCompOk nn dv, 0, true) := by
  rw [tScan_take_succ p j _ hc, hf]
  simp [tStep]

/-- Another byte: the component grows. -/
theorem tScan_other (p : GoString) (j : Nat) (c : w8) (hc : p[j + 1]? = some c) (hc' : c ≠ W8 47)
    (okv : Bool) (nn : Nat) (dv : Bool)
    (hf : ((p.drop 1).take j).foldl tStep (true, 0, true) = (okv, nn, dv)) :
    ((p.drop 1).take (j + 1)).foldl tStep (true, 0, true) = (okv, nn + 1, dv && decide (c = W8 46)) := by
  rw [tScan_take_succ p j _ hc, hf]
  have h1 : ¬ c = slash := hc'
  simp only [tStep, h1, ↓reduceIte]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem dirOk.wp_proof (wp_compOk : compOk.spec (GF := GF) (hG := hG)) :
    dirOk.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_if_destruct
  · -- `len(p) == 0`
    try wp_auto
    iapply HΦ; ipureintro; intro h; cases h
  have Hne := Hif
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · -- `len(p) >= maxDir`
    try wp_auto
    iapply HΦ; ipureintro; intro h; cases h
  have hlt : p.length < 4000 := by revert Hif; word
  have hpos : 0 < p.length := by
    rcases Nat.eq_zero_or_pos p.length with h | h
    · exact absurd (by rw [h]; rfl) Hne
    · exact h
  obtain ⟨c0, hc0⟩ : ∃ c0, p[0]? = some c0 := ⟨_, List.getElem?_eq_getElem hpos⟩
  try wp_auto
  simp only [hc0]
  try wp_auto
  wp_if_destruct
  rotate_left
  · -- `p[0] != '/'`
    try wp_auto
    iapply HΦ; ipureintro; intro h; cases h
  have h0 : p[0]? = some slash := hc0
  try wp_auto
  ihave HI : (∃ (j : Nat) (okv : Bool) (nv : w64) (dv : Bool),
      "i" ∷ i_ptr ↦ W64 ((j + 1 : Nat) : Int) ∗ "ok" ∷ ok_ptr ↦ okv ∗ "n" ∷ n_ptr ↦ nv ∗
      "dots" ∷ dots_ptr ↦ dv ∗
      "%Hj" ∷ ⌜j + 1 ≤ p.length ∧ uint.nat nv ≤ j ∧
        ((p.drop 1).take j).foldl tStep (true, 0, true) = (okv, uint.nat nv, dv)⌝ : IProp GF)
      $$ [i ok n dots]
  · iexists 0, true, W64 0, true
    rw [show (((0 + 1 : Nat)) : Int) = 1 from rfl]
    iframe
    ipureintro
    exact ⟨by omega, by simp, by simp⟩
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  obtain ⟨Hj1, Hj2, Hj3⟩ := Hj
  wp_if_destruct
  · -- `i < len(p)`
    simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have hjl : j + 1 < p.length := by revert Hif; word
    have hk : sint.nat (W64 ((j + 1 : Nat) : Int)) = j + 1 := by word
    have hk0 : 0 ≤ sint.Z (W64 ((j + 1 : Nat) : Int)) := by word
    obtain ⟨c, hc⟩ : ∃ c, p[j + 1]? = some c := ⟨_, List.getElem?_eq_getElem hjl⟩
    try wp_auto
    simp only [hk, hk0, ↓reduceIte, hc]
    try wp_auto
    have hi1 : W64 ((j + 1 + 1 : Nat) : Int) = W64 ((j + 1 : Nat) : Int) + W64 1 := by word
    wp_if_destruct
    · -- `p[i] == '/'`
      cases okv with
      | true =>
        try wp_auto
        wp_apply wp_compOk
        try wp_auto
        wp_for_post
        iframe
        iexists j + 1, tCompOk (uint.nat nv) dv, W64 0, true
        rw [hi1]
        iframe
        ipureintro
        refine ⟨by omega, by simp, ?_⟩
        simpa using tScan_slash p j hc true (uint.nat nv) dv Hj3
      | false =>
        try wp_auto
        wp_for_post
        iframe
        iexists j + 1, false, W64 0, true
        rw [hi1]
        iframe
        ipureintro
        refine ⟨by omega, by simp, ?_⟩
        simpa using tScan_slash p j hc false (uint.nat nv) dv Hj3
    · -- another byte
      have hn : uint.nat (nv + W64 1) = uint.nat nv + 1 := by word
      have hst := tScan_other p j c hc Hif okv (uint.nat nv) dv Hj3
      cases dv with
      | true =>
        try wp_auto
        simp only [hk, hk0, ↓reduceIte, hc]
        try wp_auto
        wp_for_post
        iframe
        iexists j + 1, okv, nv + W64 1, decide (c = W8 46)
        rw [hi1]
        iframe
        ipureintro
        refine ⟨by omega, by omega, ?_⟩
        rw [hn]; simpa using hst
      | false =>
        try wp_auto
        wp_for_post
        iframe
        iexists j + 1, okv, nv + W64 1, false
        rw [hi1]
        iframe
        ipureintro
        refine ⟨by omega, by omega, ?_⟩
        rw [hn]; simpa using hst
  · -- the end
    simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have hje : j + 1 = p.length := by revert Hif; word
    simp only [decide_eq_true_eq, Hif, ↓reduceIte]
    cases okv with
    | true =>
      try wp_auto
      wp_apply wp_compOk
      try wp_auto
      iapply HΦ
      ipureintro
      intro hb
      exact tDirOk_of_end p j hje hlt h0 true (uint.nat nv) dv Hj3 (by simpa using hb)
    | false =>
      try wp_auto
      iapply HΦ
      ipureintro
      intro h; cases h

end proof

end etcd_wal
end EtcdGrove
end Perennial
