/-
`fmt.Sprintf("%d.tmp", n)` of an `int` (the WAL's `filePipeline.alloc`, file_pipeline.go:77:
`fmt.Sprintf("%d.tmp", fp.count%2)`): over Perennial's `fmt.wp_Sprintf`, whose model formats `%d`
exactly, the decimal of `n` and `.tmp` (`fmt.wp_SprintfTmp`, proved; no new trust). WAL leaf
specs, 2026-11-13; Lean-first.
-/
module

public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- A format without `%` and no arguments is copied. -/
theorem fmt.SprintfOut_plain {f out : GoString} (hf : ∀ c ∈ f, c ≠ W8 37)
    (h : _root_.Perennial.fmt.SprintfOut f [] out) : out = f := by
  induction f generalizing out with
  | nil => exact _root_.Perennial.fmt.SprintfOut.done_inv h
  | cons c f ih =>
    obtain ⟨out', rfl, h'⟩ := _root_.Perennial.fmt.SprintfOut.byte_inv
      (hf c (List.mem_cons_self ..)) h
    rw [ih (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc')) h']

/-- `Sprintf("%d.tmp", n)` of an `int` is `n`'s decimal and `.tmp`. -/
theorem fmt.SprintfOut_dtmp [go.IntoValInj w64] (n : w64) (out : GoString)
    (h : _root_.Perennial.fmt.SprintfOut go!"%d.tmp" [interface.mkOk go.int #n] out) :
    out = _root_.Perennial.fmt.decimal (sint.Z n) ++ go!".tmp" := by
  have hf : go!"%d.tmp" = W8 37 :: go!"d.tmp" := rfl
  rw [hf] at h
  obtain ⟨out', rfl, h'⟩ := _root_.Perennial.fmt.SprintfOut.int_inv
    (f := go!"d.tmp") (rest := go!".tmp") (w := 0) (by decide)
    (_root_.Perennial.fmt.IntArgValue.int n)
    (_root_.Perennial.fmt.IntArgValue.uniq_int n) h
  rw [fmt.SprintfOut_plain (by decide) h', _root_.Perennial.fmt.decimalPad_zero]

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **`fmt.Sprintf("%d.tmp", n)`** of an `int` returns `n`'s decimal and `.tmp`. -/
theorem fmt.wp_SprintfTmp (n : w64) (sl : GoSlice) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ sl ↦*{dq} [interface.mkOk go.int #n] }}
      (App (App (Val (@! _root_.Perennial.fmt.Sprintf)) (Val #(go!"%d.tmp"))) (Val #sl))
    {{ (r : GoString), RET #r; sl ↦*{dq} [interface.mkOk go.int #n] ∗
        ⌜r = _root_.Perennial.fmt.decimal (sint.Z n) ++ go!".tmp"⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hsl⟩ HΦ
  wp_apply _root_.Perennial.fmt.wp_Sprintf go!"%d.tmp" sl [interface.mkOk go.int #n] dq
    (_root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (_root_.Perennial.fmt.IntArgValue.int n)
      _root_.Perennial.fmt.ArgsWf.nil) $$ [$Hsl] as %r ⟨Hsl, %hr⟩
  iapply HΦ
  iframe Hsl
  ipureintro; exact fmt.SprintfOut_dtmp n r hr

end spec

end EtcdGrove
end Perennial
