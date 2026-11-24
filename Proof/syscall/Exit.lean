/-
Proof of `Spec/syscall/Exit.lean`: its trusted model, `AngelicExit` (zap-z2, 2026-11-23).
-/
module

public import Spec.syscall.Exit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.syscall.Assumptions]

theorem syscall.Exit.wp_proof : syscall.Exit.spec (GF := GF) (hG := hG) := fun code => by
  wp_start
  iapply wp_AngelicExit

end proof

end EtcdGrove
end Perennial
