/- Lean-first (no Rocq counterpart). The proof of `hsEmpty`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.hsEmpty

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

theorem hsEmpty.wp_proof : hsEmpty.spec (GF := GF) (hG := hG) := by
  intro h
  wp_start
  wp_auto
  wp_if_destruct
  · wp_if_destruct
    · rw [show decide (h.commit' = W64 0) = tHsEmpty h by unfold tHsEmpty; simp_all]
      wp_end
    · rw [show false = tHsEmpty h by unfold tHsEmpty; simp_all]
      wp_end
  · rw [show false = tHsEmpty h by unfold tHsEmpty; simp_all]
    wp_end

end proof

end etcd_wal
end EtcdGrove
end Perennial
