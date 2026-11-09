/- Lean-first (no Rocq counterpart). The proof of `pick`: `pick.specW`'s (`pickW.lean`, the one
proof of `pick`), through `pick.spec_of_specW`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pick
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.pickW

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem pick.wp_proof
    (wp_choose : choose.spec (GF := GF) (hG := hG)) :
    pick.spec (GF := GF) (hG := hG) :=
  pick.spec_of_specW (pick.wp_proofW wp_choose)

end proof

end mvccfull
end EtcdGrove
end Perennial
