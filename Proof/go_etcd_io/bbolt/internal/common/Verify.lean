/-
`Verify`'s proof (`internal/common/verify.go`): both branches (`f` run, or not), over `os.Getenv`'s
and `strings.ToLower`'s trust-boundary specs (`Spec/os/Getenv.lean`, `Spec/strings/ToLower.lean`).
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Verify
public import Spec.os.Getenv
public import Spec.strings.ToLower

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem Verify.wp_proof (hGetenv : os.Getenv.spec (GF := GF) (hG := hG))
    (hLower : strings.ToLower.spec (GF := GF) (hG := hG)) :
    Verify.spec (GF := GF) (hG := hG) := by
  intro f Q
  wp_start as Hf
  wp_auto
  wp_func_call
  wp_call
  simp only [ENV_VERIFY_VALUE_ASSERT, ENV_VERIFY_VALUE_ALL]
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  wp_apply hGetenv as %v -
  wp_apply hLower as %lv -
  by_cases hall : lv = [97#8, 108#8, 108#8]
  · rw [decide_eq_true hall]
    wp_auto
    icases Hf with ⟨Hf, -⟩
    wp_bind (App (Val #f) (Val #()))
    iapply (wp_wand) $$ Hf
    iintro %v ⟨%hv, HQ⟩
    wp_auto
    iapply HΦ; iexact HQ
  · rw [decide_eq_false hall]
    wp_auto
    wp_apply hLower as %av -
    by_cases hon : lv = av
    · rw [decide_eq_true hon]
      wp_auto
      icases Hf with ⟨Hf, -⟩
      wp_bind (App (Val #f) (Val #()))
      iapply (wp_wand) $$ Hf
      iintro %v ⟨%hv, HQ⟩
      wp_auto
      iapply HΦ; iexact HQ
    · rw [decide_eq_false hon]
      wp_auto
      icases Hf with ⟨-, HQ⟩
      iapply HΦ; iexact HQ

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
