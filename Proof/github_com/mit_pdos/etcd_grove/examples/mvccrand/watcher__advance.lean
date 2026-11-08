/- Lean-first (no Rocq counterpart). The proof of `watcher.advance`: its two arms. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.watcher__advance

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem watcher.advance.wp_proof : watcher.advance.spec (GF := GF) (hG := hG) := by
  intro w wv r
  wp_start as Hw
  wp_auto
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    unfold advW
    simp only [Hif, ↓reduceIte]
    rw [show (W64 0 + W64 1 : w64) = W64 1 from by decide]
    iexact Hw
  · (try wp_auto)
    iapply HΦ
    unfold advW
    simp only [Hif, ↓reduceIte]
    iexact Hw

end proof

end mvccrand
end EtcdGrove
end Perennial
