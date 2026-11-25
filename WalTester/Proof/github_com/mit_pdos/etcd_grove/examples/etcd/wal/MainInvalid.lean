/- Lean-first (no Rocq counterpart). `Main.wp_proofInvalid`: `dirOk` accepts both directories only when
the tester's facts hold of them (`tArgsOk_of`), so `Main` returns. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.MainInvalid
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.dirOk

@[expose] public section

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

theorem Main.wp_proofInvalid (wp_dirOk : dirOk.spec (GF := GF) (hG := hG)) :
    Main.specInvalid (GF := GF) (hG := hG) := by
  intro e hbad
  wp_start
  wp_auto
  wp_apply wp_dirOk as %b1 %h1
  cases b1 with
  | false => try wp_auto; iapply HΦ; itrivial
  | true =>
    try wp_auto
    wp_apply wp_dirOk as %b2 %h2
    cases b2 with
    | false => try wp_auto; iapply HΦ; itrivial
    | true => exact absurd (tArgsOk_of e (h1 rfl) (h2 rfl)) hbad

end proof

end etcd_wal
end EtcdGrove
end Perennial
