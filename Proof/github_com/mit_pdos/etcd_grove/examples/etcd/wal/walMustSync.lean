/- Lean-first (no Rocq counterpart). The proof of `walMustSync`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walMustSync
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

theorem walMustSync.wp_proof (wp_hsEmpty : hsEmpty.spec (GF := GF) (hG := hG)) :
    walMustSync.spec (GF := GF) (hG := hG) := by
  intro last h n
  wp_start
  ihave HΦ := ret_gen _ _ _ $$ HΦ
  wp_auto
  wp_if_destruct
  · wp_end
    iframe; ipureintro
    have : 0 < sint.nat n := by word
    simp [tMustSync, this]
  · wp_apply wp_hsEmpty
    have h0 : sint.nat n = 0 := by word
    cases he : tHsEmpty h <;> wp_auto
    · wp_if_destruct
      · wp_end
        iframe; ipureintro; simp only [tMustSync, h0]; simp_all
      · wp_end
        iframe; ipureintro; simp only [tMustSync, h0]; simp_all
    · wp_end
      iframe; ipureintro; simp only [tMustSync, h0]; simp_all

end proof

end etcd_wal
end EtcdGrove
end Perennial
