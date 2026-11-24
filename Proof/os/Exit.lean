/-
Proof of `Spec/os/Exit.lean` over the translated `os.Exit` (zap-z2, 2026-11-23, as Perennial's
`Proof/os/Exit.lean`): `testlog.PanicOnExit0` (Perennial's linked result: false), the trusted
`runtime_beforeExit` (nothing), `syscall.Exit` (never returns).
-/
module

public import Spec.os.Exit
public import Spec.syscall.Exit
public import Perennial.Proof.internal.testlog.Link

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
variable [package_sem : _root_.Perennial.os.Assumptions]

theorem os.Exit.wp_proof
    (wp_syscall_Exit : syscall.Exit.spec (GF := GF) (hG := hG)) :
    os.Exit.spec (GF := GF) (hG := hG) := fun code => by
  wp_start
  wp_auto
  wp_bind (If _ _ _)
  wp_if_destruct
  · wp_apply internal.testlog.wp_PanicOnExit0 $$ [$Hpkg]
    -- runtime_beforeExit: its trusted model does nothing
    wp_func_call
    wp_call
    wp_auto
    wp_apply wp_syscall_Exit as Hf
    iexfalso
    iexact Hf
  · -- runtime_beforeExit: its trusted model does nothing
    wp_func_call
    wp_call
    wp_auto
    wp_apply wp_syscall_Exit as Hf
    iexfalso
    iexact Hf

end proof

end EtcdGrove
end Perennial
