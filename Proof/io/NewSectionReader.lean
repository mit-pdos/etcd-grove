/-
`io.NewSectionReader`, proved over Perennial's translation of Go's (`io/io.go`): a fresh
`&SectionReader{r, off, off, off + n, n}` (`io.secReader`). An axiom until 2026-11-21 (S4,
2026-11-18).
-/
module

public import Spec.io.NewSectionReader

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.io.Assumptions]

theorem io.NewSectionReader.wp_proof : io.NewSectionReader.spec (GF := GF) (hG := hG) := by
  intro r off n hoff hn hsum
  wp_start
  wp_auto
  rw [decide_eq_true (show sint.Z off ≤ sint.Z (W64 9223372036854775807 - n) by
    have : sint.Z (W64 9223372036854775807 - n) = 9223372036854775807 - sint.Z n := by word
    rw [this]
    have h1 : sint.Z off = off.toNat := by word
    have h2 : sint.Z n = n.toNat := by word
    omega)]
  wp_auto
  iapply HΦ
  unfold io.secReader
  rw [show n + off = off + n by word]
  iframe «$r0»
  ipureintro; exact ⟨hoff, hn, hsum⟩

end proof

end EtcdGrove
end Perennial
