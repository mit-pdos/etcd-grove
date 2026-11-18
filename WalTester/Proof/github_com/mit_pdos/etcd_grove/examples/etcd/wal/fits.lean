/- Lean-first (no Rocq counterpart). The proof of `fits` (2026-11-15): `encodeOracle`, `len`, the
comparison. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.fits
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.encodeOracle

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem fits_iff (n : Nat) (r : w64) (hn : n < 2 ^ 63) (hr : uint.nat r ≤ 2 ^ 62) :
    decide (uint.Z (W64 n + r) ≤ uint.Z (W64 0x40000000)) = true ↔ n + uint.nat r ≤ 0x40000000 := by
  simp only [decide_eq_true_eq]
  word

theorem fits.wp_proof (wp_enc : encodeOracle.spec (GF := GF) (hG := hG)) :
    fits.spec (GF := GF) (hG := hG) := by
  intro v o room hr
  wp_start as Hrep
  wp_auto
  wp_apply wp_enc $$ [$Hrep] as Hrep
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %hlen
  iapply HΦ
  iframe
  ipureintro
  exact fits_iff _ room hlen hr

end proof

end etcd_wal
end EtcdGrove
end Perennial
