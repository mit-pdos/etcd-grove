/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/putgetk/Name.lean`: `"putgetk-" +
strconv.FormatUint(i, 10)`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Name
public import Spec.strconv.FormatUint

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]

theorem Name.wp_proof
    (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    Name.spec (GF := GF) (hG := hG) := by
  intro i
  wp_start as #Hpkg
  ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_FormatUint as %str %Hstr
  · iframe #
    ipureintro
    decide
  subst Hstr
  have Hn : nameOf (uint.nat i) = go!"putgetk-" ++ fmtUint i (W64 10) := by
    have Hi : (W64 (uint.nat i)) = i := by word
    unfold nameOf
    rw [Hi]
  rw [← Hn]
  iapply HΦ
  itrivial

end proof

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
