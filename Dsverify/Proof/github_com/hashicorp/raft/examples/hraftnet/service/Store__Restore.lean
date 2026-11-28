/-
The proof of `service.Store.Restore` (adapted from dsverify-lab's hr3 `store__Restore.lean`, 241f27e):
the snapshot's bytes `b` (`snapP`) are `snapBytes es` for a committed prefix `es` ending with a
command: `Itoa |es|`, `|`, the encoded register. The parse finds the first `|` right after the
digits (no digit is `|`), `Atoi` gives back `|es|` (`strconv.Atoi_dec.spec`), and the encoded state
is non-empty; so no panic. The register becomes `regOf es`; the applied index moves from `k0` to
`|es|` (`k0 ≤ |es|`: `cmd_not_between`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.Store__Restore
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.ReadAll
public import Spec.strconv.Atoi_dec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace github_com.hashicorp.raft.examples.hraftnet.service

open github_com.hashicorp.raft proto gprot

/-! ## The snapshot's bytes, pure -/

theorem fmtNat_digits (m : Nat) (hm : m < 2 ^ 62) :
    ∀ c ∈ _root_.Perennial.internal.strconv.fmtInt (W64 (m : Int)) (W64 10), 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  have hpos : ¬ sint.Z (W64 (m : Int)) < 0 := by word
  unfold _root_.Perennial.internal.strconv.fmtInt _root_.Perennial.internal.strconv.fmtUint
  rw [if_neg hpos, dif_pos (by decide)]
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  have hd10 := _root_.Perennial.internal.strconv.baseDigits_lt _ _ _ d hd
  have hd10' : d < 10 := by simpa using hd10
  unfold _root_.Perennial.internal.strconv.digitChar
  rw [if_pos hd10']
  constructor <;> simp <;> omega

theorem fmtNat_ne_nil (m : Nat) (hm : m < 2 ^ 62) :
    _root_.Perennial.internal.strconv.fmtInt (W64 (m : Int)) (W64 10) ≠ [] := by
  have hpos : ¬ sint.Z (W64 (m : Int)) < 0 := by word
  unfold _root_.Perennial.internal.strconv.fmtInt _root_.Perennial.internal.strconv.fmtUint
  rw [if_neg hpos, dif_pos (by decide)]
  simp only [ne_eq, List.map_eq_nil_iff]
  exact _root_.Perennial.internal.strconv.baseDigits_ne_nil _ _ _

theorem fmtNat_no_bar (m : Nat) (hm : m < 2 ^ 62) :
    ∀ c ∈ _root_.Perennial.internal.strconv.fmtInt (W64 (m : Int)) (W64 10), c ≠ W8 124 := by
  intro c hc h
  have := fmtNat_digits m hm c hc
  subst h
  simp at this

theorem encodeReg_ne_nil (r : Reg) : encodeReg r ≠ [] := by
  cases r <;> simp [encodeReg]

theorem snapBytes_split (es : RLog) :
    snapBytes es = _root_.Perennial.internal.strconv.fmtInt (W64 (es.length : Int)) (W64 10) ++
      [W8 124] ++ encodeReg (regOf es) := by
  unfold snapBytes
  rfl

theorem encodeReg_head (r : Reg) :
    (encodeReg r)[0]? = some (if r.isSome then W8 49 else W8 48) := by
  cases r <;> simp [encodeReg] <;> rfl

theorem encodeReg_tail (r : Reg) : (encodeReg r).drop 1 = r.getD [] := by
  cases r <;> simp [encodeReg] <;> rfl

theorem w64_succ (a b : w64) (h0 : 0 ≤ sint.Z a) (h : sint.Z a < sint.Z b) :
    sint.Z (a + W64 1) = sint.Z a + 1 ∧ sint.nat (a + W64 1) = sint.nat a + 1 := by
  constructor <;> word

theorem not_neg_of_nonneg (a : w64) (h : 0 ≤ sint.Z a) : ¬ (sint.Z a < sint.Z (W64 0)) := by
  rw [show sint.Z (W64 0) = 0 from rfl]; omega

theorem nonneg_of_lt62 (m : Nat) (h : m < 2 ^ 62) : 0 ≤ sint.Z (W64 (m : Int)) := by word

theorem sint_Z_lt (a : w64) : sint.Z a < 2 ^ 63 := by word

theorem sint_nat_eq (a : w64) (h0 : 0 ≤ sint.Z a) : (sint.nat a : Int) = sint.Z a :=
  Int.toNat_of_nonneg h0

end github_com.hashicorp.raft.examples.hraftnet.service

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

set_option goose.wp.extras true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

theorem github_com.hashicorp.raft.examples.hraftnet.service.Store.Restore.wp_proof
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_ReadAll : github_com.hashicorp.raft.examples.snapstore.ReadAll.spec (GF := GF) (hG := hG))
    (wp_Atoi : strconv.Atoi_dec.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.service.Store.Restore.spec (GF := GF) (hG := hG) := by
  intro γ fc alb i s k0 x rd R b eof
  wp_start as ⟨#Hst, Hown, %Hk0, #Heof, #Hrd, HR, #Hsnap⟩
  unfold isStore
  icases Hst with ⟨#Hlock, #Hfr, #Hls, #Hdb⟩
  ihave #Hss : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore $$ []
  · iPkgInit
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply (wp_ReadAll rd R b eof) $$ [$HR] as %sl ⟨Hsl, HR⟩
  · iframe #
    unfold readCloserOk
    icases Hrd with ⟨#Hrd, -⟩
    iframe #
  unfold readCloserOk
  icases Hrd with ⟨-, #HClose⟩
  wp_bind (App (Val #(methods rd.ty _ rd.v)) _)
  iapply HClose
  wp_auto
  unfold snapP
  icases Hsnap with ⟨%es, %Hes, #Hpre, #Hflb, #Hnc⟩
  obtain ⟨Hesx, Hb, Hes62, Hlast⟩ := Hes
  subst Hb
  rw [snapBytes_split]
  ihave %Hslen := ownSlice_len _ _ _ $$ Hsl
  generalize hD : _root_.Perennial.internal.strconv.fmtInt (W64 (es.length : Int)) (W64 10) = D at Hslen ⊢
  have hDne : D ≠ [] := hD ▸ fmtNat_ne_nil _ Hes62
  have hDbar : ∀ c ∈ D, c ≠ W8 124 := hD ▸ fmtNat_no_bar _ Hes62
  have hEne := encodeReg_ne_nil (regOf es)
  have hEpos : 0 < (encodeReg (regOf es)).length := List.length_pos_iff.2 hEne
  have hDpos : 0 < D.length := List.length_pos_iff.2 hDne
  simp only [List.length_append, List.length_singleton] at Hslen
  have hsll := sint_nat_eq sl.len Hslen.2
  ihave HI : (∃ (kk : w64), "k" ∷ k_ptr ↦ kk ∗
      "%Hkk" ∷ ⌜0 ≤ sint.Z kk ∧ sint.nat kk ≤ D.length⌝ : IProp GF) $$ [k]
  · iexists W64 0
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · rw [if_pos (by word)]
    have hkn : (sint.Z kk).toNat = sint.nat kk := rfl
    by_cases hlt : sint.nat kk < D.length
    · have hc : (D ++ [W8 124] ++ encodeReg (regOf es))[(sint.Z kk).toNat]? = some D[sint.nat kk] := by
        rw [hkn, List.append_assoc, List.getElem?_append_left hlt]; simp
      have hcb : D[sint.nat kk] ≠ W8 124 := hDbar _ (List.getElem_mem _)
      wp_apply (wp_load_slice_index sl (sint.Z kk) _ (DFrac.own 1) D[sint.nat kk] Hkk.1) $$ [$Hsl] as Hsl
      · ipureintro; exact hc
      simp only [hcb, decide_False_any, decide_True_any, Bool.not_false, Bool.not_true, intoVal_eq_iff, decide_eq_self_any, ↓reduceIte]
      wp_auto
      wp_for_post
      iframe
      iexists kk + W64 1
      iframe
      have hs := w64_succ kk sl.len Hkk.1 (by have := sint_nat_eq kk Hkk.1; omega)
      ipureintro; omega
    · have hkD : sint.nat kk = D.length := by omega
      have hc : (D ++ [W8 124] ++ encodeReg (regOf es))[(sint.Z kk).toNat]? = some (W8 124) := by
        rw [hkn, hkD, List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]; simp
      wp_apply (wp_load_slice_index sl (sint.Z kk) _ (DFrac.own 1) (W8 124) Hkk.1) $$ [$Hsl] as Hsl
      · ipureintro; exact hc
      simp only [decide_False_any, decide_True_any, Bool.not_false, Bool.not_true, intoVal_eq_iff,
        decide_eq_self_any, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      have hk0 : kk ≠ W64 0 := by
        intro h; subst h; have : sint.nat (W64 0) = 0 := rfl; omega
      have hkZ : sint.Z kk = (D.length : Int) := by rw [← sint_nat_eq kk Hkk.1, hkD]
      have hs1 := w64_succ kk sl.len Hkk.1 (by omega)
      have hge : ¬ (sint.Z sl.len ≤ sint.Z (kk + W64 1)) := by omega
      simp only [hk0, decide_False_any, decide_True_any, Bool.not_false, Bool.not_true,
        intoVal_eq_iff, decide_eq_self_any, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      simp only [hge, decide_False_any, ↓reduceIte]
      wp_auto
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
      imod ownSlice_persist $$ Hsl with #Hsl
      have hb1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z kk ∧ sint.Z kk ≤ sint.Z sl.len := by
        refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega, ?_⟩
        rw [hkZ, ← hsll, ← Hslen.1]; omega
      have hb2 : 0 ≤ sint.Z (kk + W64 1) ∧ sint.Z (kk + W64 1) ≤ sint.Z sl.len ∧
          sint.Z sl.len ≤ sint.Z sl.len := by
        refine ⟨by omega, ?_, Int.le_refl _⟩
        rw [hs1.1, hkZ, ← hsll, ← Hslen.1]; omega
      icases (ownSlice_slice (W64 0) kk sl DFrac.discard _ hb1).1 $$ Hsl with ⟨-, #Hs1, -⟩
      icases (ownSlice_slice (kk + W64 1) sl.len sl DFrac.discard _ hb2).1 $$ Hsl with ⟨-, #Hs2, -⟩
      have h0 : sint.nat (W64 0) = 0 := rfl
      have hsub1 : subslice (sint.nat (W64 0)) (sint.nat kk) (D ++ [W8 124] ++ encodeReg (regOf es)) = D := by
        rw [h0, hkD]; simp [subslice]
      have hsub2 : subslice (sint.nat (kk + W64 1)) (sint.nat sl.len) (D ++ [W8 124] ++ encodeReg (regOf es)) =
          encodeReg (regOf es) := by
        rw [hs1.2, hkD, ← Hslen.1]
        unfold subslice
        rw [List.take_of_length_le (by simp; omega), List.drop_left' (by simp)]
      rw [hsub1] at *
      rw [hsub2] at *
      rw [if_pos (by constructor <;> omega)]
      wp_apply (wp_bytes_to_string _ D DFrac.discard) $$ [$Hs1] as -
      have hes0 := nonneg_of_lt62 es.length Hes62
      rw [← hD]
      wp_apply (wp_Atoi (W64 (es.length : Int)) hes0) $$ [$Hstr]
      have hneg := not_neg_of_nonneg _ hes0
      simp only [hneg, decide_False_any, ↓reduceIte]
      wp_auto
      rw [if_pos ⟨hb2.1, hb2.2.1, Hwf.2⟩]
      wp_apply (wp_bytes_to_string _ (encodeReg (regOf es)) DFrac.discard) $$ [$Hs2] as -
      wp_apply wp_Mutex_Lock $$ [$Hlock] as ⟨Hlocked, Hinv⟩
      unfold storeInv fsmOwn
      icases Hinv with ⟨%es0, #Hpre0, #Hflb0, Halb2, Hpres, Hval, Hidx, %Hes0⟩
      ihave %Hag := monoNatAuthOwn_agree _ _ _ _ _ $$ Hown Halb2
      have Hk0e : es0.length = k0 := Hag.2.symm
      subst Hk0e
      ihave %Hfwd := cmd_not_between γ es0 es.length x Hes0.2 Hk0 $$ [Hpre0 Hnc]
      · iframe #
      ihave Halb := monoNat_halves _ _ $$ [Hown Halb2]
      · iframe
      imod mono_nat_own_update es.length Hfwd $$ Halb with ⟨Halb, #Hlb⟩
      ihave ⟨Halb, Halb2⟩ := monoNat_split _ _ $$ Halb
      wp_auto
      rw [encodeReg_head]
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hstlen
      have hE62 : (encodeReg (regOf es)).length < 2 ^ 63 := by
        have := sint_Z_lt sl.len; omega
      have hc : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z (W64 ((encodeReg (regOf es)).length : Int)) ∧
          sint.Z (W64 ((encodeReg (regOf es)).length : Int)) ≤ ((encodeReg (regOf es)).length : Int) := by
        refine ⟨by word, by word, by word⟩
      have hv : List.take (sint.nat (W64 ((encodeReg (regOf es)).length : Int)) - sint.nat (W64 1))
          (List.drop (sint.nat (W64 1)) (encodeReg (regOf es))) = (regOf es).getD [] := by
        rw [show sint.nat (W64 1) = 1 from rfl, encodeReg_tail]
        apply List.take_of_length_le
        have : sint.nat (W64 ((encodeReg (regOf es)).length : Int)) = (encodeReg (regOf es)).length := by word
        rw [this, ← encodeReg_tail, List.length_drop]; exact Nat.le_refl _
      simp only [hc, _root_.and_self, ↓reduceIte]
      wp_auto
      rw [show sint.nat (W64 1) = 1 from rfl] at hv
      rw [hv]
      have hpres : decide ((if (regOf es).isSome = true then W8 49 else W8 48) = W8 49) =
          (regOf es).isSome := by
        cases (regOf es).isSome <;> decide
      rw [hpres]
      wp_apply wp_Mutex_Unlock $$ [$Hlock $Hlocked Halb2 Hpres Hval Hidx]
      · inext; iexists es; iframe; iframe #; ipureintro; exact ⟨Hes62, Hlast⟩
      try wp_auto
      iapply HΦ
      iexists es.length, interface.mkOk result.ty #(respAt es)
      iframe
      iframe #
      isplitr
      · ipureintro; exact Hesx
      iright
      unfold respP appliedLb
      iexists es
      iframe #
      ipureintro; exact ⟨rfl, rfl⟩
  · exfalso; word

end proof

end Perennial
