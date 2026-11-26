/- Lean-first (no Rocq counterpart). The proof of `inScope`: its checks, then `runCfgOk_of`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inScope
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.hashing
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.weightsFit
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.ScopeLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem inScope.wp_proof (wp_hashing : hashing.spec (GF := GF) (hG := hG))
    (wp_weightsFit : weightsFit.spec (GF := GF) (hG := hG)) :
    inScope.spec (GF := GF) (hG := hG) := by
  intro cfg wr dq
  wp_start as Hw
  wp_auto
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ; iframe; ipureintro; intro h; cases h
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
