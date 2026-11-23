/-
`fmt.Sprintf("%s.broken.%v", d, s)` of two strings (the WAL's `cleanupWAL`): proved over Perennial's
`Sprintf` model, which since `79517dbdf` (fmtmodel, 2026-11-20) formats `%v` of a string as `%s`
(`SprintfOut.strV`). Until then a hypothesis (`notes/perennial-changes.md`, "`Sprintf`'s `%v` of a
string"). Lean-first.
-/
module

public import Spec.fmt.SprintfBroken
public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- `Sprintf("%s.broken.%v", d, s)` of two strings is `d ++ ".broken." ++ s`. -/
theorem fmt.SprintfOut_broken [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] [go.IntoValInj GoString] [go.string ↓u go.string] (d s out : GoString)
    (h : _root_.Perennial.fmt.SprintfOut go!"%s.broken.%v"
      [interface.mkOk go.string #d, interface.mkOk go.string #s] out) :
    out = d ++ go!".broken." ++ s := by
  have hf : go!"%s.broken.%v" = W8 37 :: W8 115 :: go!".broken.%v" := rfl
  rw [hf] at h
  obtain ⟨o1, rfl, h1⟩ := _root_.Perennial.fmt.SprintfOut.str_inv h
  -- the eight plain bytes `.broken.`
  have hb : go!".broken.%v" = go!".broken." ++ (W8 37 :: W8 118 :: []) := rfl
  rw [hb] at h1
  suffices H : ∀ (p : GoString), (∀ c ∈ p, c ≠ W8 37) → ∀ o,
      _root_.Perennial.fmt.SprintfOut (p ++ (W8 37 :: W8 118 :: []))
        [interface.mkOk go.string #s] o → o = p ++ s by
    rw [H _ (by decide) o1 h1, List.append_assoc]
  intro p hp
  induction p with
  | nil =>
    intro o ho
    obtain ⟨o2, rfl, h2⟩ := _root_.Perennial.fmt.SprintfOut.strV_inv ho
    rw [_root_.Perennial.fmt.SprintfOut.done_inv h2, List.append_nil, List.nil_append]
  | cons c p ih =>
    intro o ho
    obtain ⟨o', rfl, h'⟩ := _root_.Perennial.fmt.SprintfOut.byte_inv (hp c (List.mem_cons_self ..)) ho
    rw [ih (fun c' hc' => hp c' (List.mem_cons_of_mem _ hc')) o' h']
    rfl

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

theorem fmt.SprintfBroken.wp_proof : fmt.SprintfBroken.spec (GF := GF) (hG := hG) := by
  intro d s sl dq
  iintro %Φ ⟨#Hpkg, Hsl⟩ HΦ
  wp_apply _root_.Perennial.fmt.wp_Sprintf_argsWf go!"%s.broken.%v" sl
    [interface.mkOk go.string #d, interface.mkOk go.string #s] dq
    (_root_.Perennial.fmt.ArgsWf.cons_string d _ (_root_.Perennial.fmt.ArgsWf.cons_string s _
      _root_.Perennial.fmt.ArgsWf.nil)) $$ [$Hsl] as %r ⟨Hsl, %hr⟩
  iapply HΦ
  iframe Hsl
  ipureintro; exact fmt.SprintfOut_broken d s r hr

end spec

end EtcdGrove
end Perennial
