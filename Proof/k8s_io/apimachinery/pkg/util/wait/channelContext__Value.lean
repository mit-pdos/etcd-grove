/-
The proof of `Spec/k8s_io/apimachinery/pkg/util/wait/channelContext__Value.lean` (translated code). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.wait.channelContext__Value

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [wait_sem : k8s_io.apimachinery.pkg.util.wait.Assumptions]

theorem wait.channelContext.Value.wp_proof : wait.channelContext.Value.spec (GF := GF) (hG := hG) := by
  intro sc key
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
