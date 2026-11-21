/-
`strconv.ParseInt`, proved over Perennial's translation of Go's (stdlib2, 2026-11-21; until then a
trust-boundary axiom); `ParseInt` reads back what `FormatInt` writes, `internal.strconv.parseInt_fmtInt10`.
-/
module

public import Spec.strconv.ParseInt
public import Perennial.Proof.strconv.Link

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
variable [package_sem : _root_.Perennial.strconv.Assumptions]

theorem strconv.ParseInt.wp_proof : strconv.ParseInt.spec (GF := GF) (hG := hG) := by
  intro s base bitSize hb1 hb2 hs1 hs2
  iintro %Φ #Hpkg HΦ
  wp_apply _root_.Perennial.strconv.wp_ParseInt s base bitSize hb1 hb2 hs1 hs2 as %n %err Hres
  iapply HΦ
  have key : ∀ m : w64, s = fmtInt m (W64 10) → base = W64 10 → bitSize = W64 64 →
      internal.strconv.parseInt s (sint.nat base) (sint.nat bitSize) = .ok (sint.Z m) := by
    intro m hs hb hbs
    subst hs hb hbs
    exact internal.strconv.parseInt_fmtInt10 m
  generalize hr : internal.strconv.parseInt s (sint.nat base) (sint.nat bitSize) = r at Hres key
  cases r with
  | ok k =>
    icases Hres with %Hk
    ipureintro
    intro m hs hb hbs
    have := key m hs hb hbs
    cases this
    refine ⟨?_, Hk.2⟩
    rw [Hk.1]
    word
  | errSyntax =>
    ipureintro
    intro m hs hb hbs
    cases key m hs hb hbs
  | errRange k =>
    ipureintro
    intro m hs hb hbs
    cases key m hs hb hbs

end proof

end EtcdGrove
end Perennial
