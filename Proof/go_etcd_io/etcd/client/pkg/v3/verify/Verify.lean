/-
`verify.Verify`'s proof (`client/pkg/verify/verify.go`; etcdstorage, 2026-11-20, until then the
trust boundary, an axiom): both branches (`f` run and its condition checked by `verifier`, or not),
over `os.Getenv`'s and `strings.ToLower`'s trust-boundary specs, as bbolt's `internal/common.Verify`.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Verify
public import Spec.os.Getenv
public import Spec.strings.ToLower

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.verify.Assumptions]

theorem verify.Verify.wp_proof (hGetenv : os.Getenv.spec (GF := GF) (hG := hG))
    (hLower : strings.ToLower.spec (GF := GF) (hG := hG)) :
    verify.Verify.spec (GF := GF) (hG := hG) := by
  intro msg f P
  wp_start as ⟨#Hinit, HP, Hf⟩
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  wp_apply hGetenv as %v -
  wp_apply hLower as %lv -
  by_cases hall : lv = go!"all"
  · rw [decide_eq_true hall]
    wp_auto
    wp_bind (App (Val f) (Val #()))
    iapply (wp_wand) $$ [Hf HP]
    · iapply Hf; iexact HP
    iintro %r ⟨%d, %hr, HP⟩
    subst hr
    wp_auto
    wp_func_call
    wp_call
    wp_auto
    iapply HΦ; iexact HP
  · rw [decide_eq_false hall]
    wp_auto
    wp_apply hLower as %av -
    by_cases hon : lv = av
    · rw [decide_eq_true hon]
      wp_auto
      wp_bind (App (Val f) (Val #()))
      iapply (wp_wand) $$ [Hf HP]
      · iapply Hf; iexact HP
      iintro %r ⟨%d, %hr, HP⟩
      subst hr
      wp_auto
      wp_func_call
      wp_call
      wp_auto
      iapply HΦ; iexact HP
    · rw [decide_eq_false hon]
      wp_auto
      iapply HΦ; iexact HP

end proof

end EtcdGrove
end Perennial
