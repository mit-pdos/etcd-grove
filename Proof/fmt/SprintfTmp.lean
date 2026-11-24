/-
`fmt.Sprintf("%d.tmp", n)` of an `int` (the WAL's `filePipeline.alloc`, file_pipeline.go:77:
`fmt.Sprintf("%d.tmp", fp.count%2)`): over Perennial's `fmt.wp_Sprintf` of the real `Sprintf` (real `fmt`
stage 1; until 2026-11-24 over its model), the decimal of `n` and `.tmp` (`fmt.wp_SprintfTmp`,
proved; no new trust). WAL leaf
specs, 2026-11-13; Lean-first.
-/
module

public import Perennial.Proof.fmt
public import Proof.fmt.SprintfPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

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
  wp_apply fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"%d.tmp"
    [.dir none _root_.Perennial.fmt.verb_d, .lit go!".tmp"] sl [interface.mkOk go.int #n] _ dq
    (by fmt_encode) (by fmt_fits) (.int _ _ _ _ (.int n) .nil) $$ [$Hsl] as %r ⟨Hsl, %hr⟩
  iapply HΦ
  iframe Hsl
  ipureintro
  simp (config := { decide := true }) [hr, _root_.Perennial.fmt.render, _root_.Perennial.fmt.dirOutFn,
    _root_.Perennial.fmt.decimalPad_zero]

end spec

end EtcdGrove
end Perennial
