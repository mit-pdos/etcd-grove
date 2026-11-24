/-
`Main.wp_proof` (W4c U5): `dirOk`'s checks, then `Boot(area, orDir, 0, 40)`. Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Main
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.dirOk

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem Main.wp_proof (wp_dirOk : dirOk.spec (GF := GF) (hG := hG))
    (wp_boot : Boot.spec (GF := GF) (hG := hG)) : Main.spec (GF := GF) (hG := hG) := by
  intro W e γ o od hf hpath hr hfs
  wp_start as ⟨Hrun⟩
  wp_auto
  wp_apply wp_dirOk as %b1 -
  cases b1 with
  | false => try wp_auto; iapply HΦ; itrivial
  | true =>
    try wp_auto
    wp_apply wp_dirOk as %b2 -
    cases b2 with
    | false => try wp_auto; iapply HΦ; itrivial
    | true =>
      try wp_auto
      wp_apply (wp_boot W e γ o od (W64 0) (W64 40) hf hpath hr hfs) $$ [Hrun] as %st -
      · iframe
      iapply HΦ; itrivial

end proof

end etcd_wal
end EtcdGrove
end Perennial
