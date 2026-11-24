/-
`fmt.Sprintf("%s.broken.%v", d, s)` of two strings (the WAL's `cleanupWAL`): proved over Perennial's
spec of the real `Sprintf` (real `fmt` stage 1, 2026-11-24; from 2026-11-20 over its model, which
formatted `%v` of a string as `%s`). Until then a hypothesis (`notes/perennial-changes.md`, "`Sprintf`'s `%v` of a
string"). Lean-first.
-/
module

public import Spec.fmt.SprintfBroken
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

theorem fmt.SprintfBroken.wp_proof : fmt.SprintfBroken.spec (GF := GF) (hG := hG) := by
  intro d s sl dq
  iintro %Φ ⟨#Hpkg, Hsl⟩ HΦ
  wp_apply fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"%s.broken.%v"
    [.dir none _root_.Perennial.fmt.verb_s, .lit go!".broken.", .dir none _root_.Perennial.fmt.verb_v]
    sl [interface.mkOk go.string #d, interface.mkOk go.string #s] _ dq
    (by fmt_encode) (by fmt_fits) (.str _ _ _ (.str _ _ _ .nil)) $$ [$Hsl] as %r ⟨Hsl, %hr⟩
  iapply HΦ
  iframe Hsl
  ipureintro
  simp (config := { decide := true }) [hr, _root_.Perennial.fmt.render, _root_.Perennial.fmt.dirOutFn]

end spec

end EtcdGrove
end Perennial
