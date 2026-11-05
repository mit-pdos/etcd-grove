/- Lean-first (no Rocq counterpart). The proof of `writer.newVal`: the count's increment, then
`itoa` of it. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__newVal

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

theorem writer.newVal.wp_proof (wp_itoa : itoa.spec (GF := GF) (hG := hG)) :
    writer.newVal.spec (GF := GF) (hG := hG) := by
  intro w n h0 h1
  wp_start as Hw
  wp_auto
  wp_apply wp_itoa (n + W64 1) (by word)
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end mvccrand
end EtcdGrove
end Perennial
