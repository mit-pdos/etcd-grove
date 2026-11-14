/- Lean-first (no Rocq counterpart). The proof of `rnd.choose`. -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__choose
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__next

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

theorem rnd.choose.wp_proof (wp_next : rnd.next.spec (GF := GF) (hG := hG)) :
    rnd.choose.spec (GF := GF) (hG := hG) := by
  intro r v n
  wp_start as Hr
  wp_auto
  wp_if_destruct
  · iapply HΦ
    isplitl [Hr]
    · iexists v; iexact Hr
    · ipureintro; simp
  · wp_apply wp_next $$ [$Hr] as %x Hr
    rw [if_neg (show ¬ uint.Z n = 0 by intro h; apply Hif; word)]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    rw [if_neg (by assumption)]
    have hn : uint.nat n ≠ 0 := by intro h; word
    rw [show uint.nat (x % n) = uint.nat x % uint.nat n by word]
    exact Nat.mod_lt _ (by omega)

end proof

end etcd_wal
end EtcdGrove
end Perennial
