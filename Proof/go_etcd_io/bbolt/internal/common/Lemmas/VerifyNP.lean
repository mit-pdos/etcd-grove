/-
`Verify` over a corrected spec (final wave D): `Verify.specNP` is `Verify.spec` with `f`'s WP
excluding a panic (`⌜v.isPanic = false⌝ ∗ Q`, in place of `Q` at any `v`). `Verify.spec` as stated
is false: `f := func() { panic(x) }` and `Q := True` meet its precondition (a WP's postcondition also
receives panics, `PanicV p`), and when `BBOLT_VERIFY` is `assert` or `all` (`os.Getenv` returns any
string) `Verify(f)` panics, where the spec promises `RET #()`. `Verify.wp_proofNP` covers both
branches (`f` run, or not) over `os.Getenv`'s and `strings.ToLower`'s trust-boundary specs.
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
namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `Verify.spec` with `f` not panicking (see the file header). -/
abbrev Verify.specNP : Prop :=
  ∀ (f : GoFunc) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗
      (WP (App (Val #f) (Val #())) {{ fun v => iprop(⌜v.isPanic = false⌝ ∗ Q) }} ∧ Q) }}
    (App (Val #(functions Verify [])) (Val #f))
  {{ RET #(); Q }}

theorem Verify.wp_proofNP (hGetenv : os.Getenv.spec (GF := GF) (hG := hG))
    (hLower : strings.ToLower.spec (GF := GF) (hG := hG)) :
    Verify.specNP (GF := GF) (hG := hG) := by
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
