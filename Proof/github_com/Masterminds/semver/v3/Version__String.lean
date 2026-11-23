/-
Proof of `Spec/github_com/Masterminds/semver/v3/Version__String.lean` over the real code
(`version.go:340-352`; prove-ps2-semstr, 2026-11-23: until then a trust-boundary axiom): three
`fmt.Fprintf`s into a `bytes.Buffer` (`fmt.Fprintf.spec`, the buffer its writer by
`bytes.Buffer.writeSpec`), then the buffer's `String()`.
-/
module

public import Spec.github_com.Masterminds.semver.v3.Version__String
public import Perennial.Spec.fmt.Fprintf
public import Perennial.Spec.bytes.Buffer__String
public import Perennial.Proof.bytes.BufferWriter

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section pure
open _root_.Perennial.fmt

/-- `Sprintf("%d.%d.%d", a, b, c)` of three `uint64`s. -/
theorem semver.sprintf_ddd [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]
    [go.IntoValInj w64] [go.string ↓u go.string] (a b c : w64) (out : GoString)
    (h : SprintfOut go!"%d.%d.%d" [interface.mkOk go.uint64 #a, interface.mkOk go.uint64 #b,
      interface.mkOk go.uint64 #c] out) :
    out = _root_.Perennial.fmt.decimal (uint.Z a) ++ go!"." ++
      _root_.Perennial.fmt.decimal (uint.Z b) ++ go!"." ++ _root_.Perennial.fmt.decimal (uint.Z c) := by
  have hfmt : go!"%d.%d.%d" = W8 37 :: W8 100 :: W8 46 :: W8 37 :: W8 100 :: W8 46 :: W8 37 :: [W8 100] := rfl
  rw [hfmt] at h
  obtain ⟨o1, rfl, h1⟩ := SprintfOut.int_inv (w := 0) (rest := W8 46 :: W8 37 :: W8 100 :: W8 46 :: W8 37 :: [W8 100])
    (by decide) (IntArgValue.uint64 a) (IntArgValue.uniq_uint64 a) h
  obtain ⟨o2, rfl, h2⟩ := SprintfOut.byte_inv (by decide) h1
  obtain ⟨o3, rfl, h3⟩ := SprintfOut.int_inv (w := 0) (rest := W8 46 :: W8 37 :: [W8 100])
    (by decide) (IntArgValue.uint64 b) (IntArgValue.uniq_uint64 b) h2
  obtain ⟨o4, rfl, h4⟩ := SprintfOut.byte_inv (by decide) h3
  obtain ⟨o5, rfl, h5⟩ := SprintfOut.int_inv (w := 0) (rest := [])
    (by decide) (IntArgValue.uint64 c) (IntArgValue.uniq_uint64 c) h4
  rw [SprintfOut.done_inv h5]
  simp [decimalPad_zero]

/-- `Sprintf(p ++ "%s", x)` of a string `x`, `p` one byte other than `%`. -/
theorem semver.sprintf_cs [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]
    [go.IntoValInj GoString] (c : w8) (hc : c ≠ W8 37) (x : GoString) (out : GoString)
    (h : SprintfOut (c :: go!"%s") [interface.mkOk go.string #x] out) :
    out = c :: x := by
  obtain ⟨o1, rfl, h1⟩ := SprintfOut.byte_inv hc h
  have hfmt : go!"%s" = W8 37 :: W8 115 :: [] := rfl
  rw [hfmt] at h1
  obtain ⟨o2, rfl, h2⟩ := SprintfOut.str_inv h1
  rw [SprintfOut.done_inv h2]
  simp

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.Masterminds.semver.v3.Assumptions]

theorem semver.Version.String.wp_proof
    (hWrite : bytes.Buffer.Write.spec (GF := GF) (hG := hG))
    (hBufString : bytes.Buffer.String.spec (GF := GF) (hG := hG))
    (hFprintf : fmt.Fprintf.spec (GF := GF) (hG := hG)) :
    semver.Version.String.spec (GF := GF) (hG := hG) := by
  intro v dq x
  wp_start as Hv
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  ihave Hb := bytes.ownBuffer_new buf_ptr $$ buf
  wp_apply wp_slice_literal (V := GoInterface)
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply hFprintf _ _ _ _ _ (bytes.ownBuffer buf_ptr [])
      (fun s n err => iprop(⌜n = W64 (s.length : Int) ∧ err = interface.nil⌝ ∗
        bytes.ownBuffer buf_ptr ([] ++ s))) $$ [Hasl Hb]
    as %n1 %e1 ⟨-, %s1, %Hs1, %-, Hb⟩
  · iframe #; iframe Hasl Hb
    simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 by rfl,
      List.set_cons_succ, List.set_cons_zero]
    isplitr
    · iapply (_root_.Perennial.fmt.argsOk_of_argsWf
        (.cons_int _ _ _ (.uint64 _) (.cons_int _ _ _ (.uint64 _) (.cons_int _ _ _ (.uint64 _) .nil))))
    iexists _
    isplitr
    · ipureintro; rfl
    iapply bytes.Buffer.writeSpec hWrite
  simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 by rfl,
    List.set_cons_succ, List.set_cons_zero] at Hs1
  rw [List.nil_append]
  -- `-pre`, if not empty
  wp_if_destruct
  have e : s1 ++ (if x.pre' = [] then [] else go!"-" ++ x.pre') = s1 := by simp [Hif]
  rw [← e]
  rotate_left
  wp_apply wp_slice_literal (V := GoInterface)
  isplitr
  · ipureintro; rfl
  iintro %asl2 ⟨Hasl2, -⟩
  wp_apply hFprintf _ _ _ _ _ (bytes.ownBuffer buf_ptr s1)
      (fun s n err => iprop(⌜n = W64 (s.length : Int) ∧ err = interface.nil⌝ ∗
        bytes.ownBuffer buf_ptr (s1 ++ s))) $$ [Hasl2 Hb]
    as %n2 %e2 ⟨-, %s2, %Hs2, %-, Hb⟩
  · iframe #; iframe Hasl2 Hb
    isplitr
    · iapply (_root_.Perennial.fmt.argsOk_of_argsWf (.cons_string _ _ .nil))
    iexists _
    isplitr
    · ipureintro; rfl
    iapply bytes.Buffer.writeSpec hWrite
  have e : s2 = (if x.pre' = [] then [] else go!"-" ++ x.pre') := by
    simp only [Hif, ↓reduceIte]; exact semver.sprintf_cs (W8 45) (by decide) _ _ Hs2
  rw [e]
  -- `+metadata`, if not empty
  all_goals
    wp_if_destruct
    have e : s1 ++ (if x.pre' = [] then [] else go!"-" ++ x.pre') ++
        (if x.metadata' = [] then [] else go!"+" ++ x.metadata') =
        s1 ++ (if x.pre' = [] then [] else go!"-" ++ x.pre') := by simp [Hif]
    rw [← e]
    rotate_left
    wp_apply wp_slice_literal (V := GoInterface)
    isplitr
    · ipureintro; rfl
    iintro %asl3 ⟨Hasl3, -⟩
    wp_apply hFprintf _ _ _ _ _
        (bytes.ownBuffer buf_ptr (s1 ++ (if x.pre' = [] then [] else go!"-" ++ x.pre')))
        (fun s n err => iprop(⌜n = W64 (s.length : Int) ∧ err = interface.nil⌝ ∗
          bytes.ownBuffer buf_ptr (s1 ++ (if x.pre' = [] then [] else go!"-" ++ x.pre') ++ s)))
        $$ [Hasl3 Hb]
      as %n3 %e3 ⟨-, %s3, %Hs3, %-, Hb⟩
    · iframe #; iframe Hasl3 Hb
      isplitr
      · iapply (_root_.Perennial.fmt.argsOk_of_argsWf (.cons_string _ _ .nil))
      iexists _
      isplitr
      · ipureintro; rfl
      iapply bytes.Buffer.writeSpec hWrite
    have e : s3 = (if x.metadata' = [] then [] else go!"+" ++ x.metadata') := by
      simp only [Hif, ↓reduceIte]; exact semver.sprintf_cs (W8 43) (by decide) _ _ Hs3
    rw [e]
  -- `buf.String()`
  all_goals
    wp_apply hBufString $$ Hb as Hb
    have e : s1 ++ (if x.pre' = [] then [] else go!"-" ++ x.pre') ++
        (if x.metadata' = [] then [] else go!"+" ++ x.metadata') = semver.render x := by
      rw [semver.sprintf_ddd _ _ _ _ Hs1]; simp only [semver.render, List.append_assoc]
    rw [e]
    iapply HΦ $$ Hv

end proof

end EtcdGrove
end Perennial
