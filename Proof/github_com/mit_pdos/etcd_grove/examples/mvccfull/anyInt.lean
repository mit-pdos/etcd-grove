/- Lean-first (no Rocq counterpart). The proof of `anyInt`: two draws, a shift. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.anyInt

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

theorem anyInt.wp_proof : anyInt.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %r1 _
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %r2 _
  (try rw [if_neg (show ¬ uint.Z (W64 64) = 0 by decide)])
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end mvccfull
end EtcdGrove
end Perennial
