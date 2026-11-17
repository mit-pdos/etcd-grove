/- Lean-first (no Rocq counterpart). The proof of `putHS` (W4c U5). -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putHS
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putU64

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

theorem putHS.wp_proof (wp_putU64 : putU64.spec (GF := GF) (hG := hG)) :
    putHS.spec (GF := GF) (hG := hG) := by
  intro b bs h
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply wp_putU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  wp_apply wp_putU64 $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
  wp_apply wp_putU64 $$ [$Hb $Hcap] as %b3 ⟨Hb, Hcap⟩
  iapply HΦ
  unfold tHsBytes
  simp only [List.append_assoc]
  iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
