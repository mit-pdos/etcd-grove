/- Lean-first (no Rocq counterpart). The proof of `rnd.next`. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__next

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

theorem rnd.next.wp_proof : rnd.next.spec (GF := GF) (hG := hG) := by
  intro r v
  wp_start as Hr
  wp_auto
  cases hs : v.seeded'
  · simp only [Bool.not_false]
    wp_auto
    wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x _
    iapply HΦ
    iexists _
    iframe
  · simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    iexists _
    iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
