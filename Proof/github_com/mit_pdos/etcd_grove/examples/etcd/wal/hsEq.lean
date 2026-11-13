/- Lean-first (no Rocq counterpart). The proof of `hsEq`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.hsEq

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

theorem hsEq.wp_proof : hsEq.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  ihave HΦ := ret_gen _ _ _ $$ HΦ
  wp_auto
  wp_if_destruct
  · wp_if_destruct
    · wp_end
      iframe; ipureintro; cases a; cases b; simp_all
    · wp_end
      iframe; ipureintro; cases a; cases b; simp_all
  · wp_end
    iframe; ipureintro; cases a; cases b; simp_all

end proof

end etcd_wal
end EtcdGrove
end Perennial
