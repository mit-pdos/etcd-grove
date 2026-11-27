/-
`verify.IsVerificationEnabled`'s proof (`client/pkg/verify/verify.go`; etcdstorage, 2026-11-20), over
`os.Getenv`'s spec (`ETCD_VERIFY`'s value is the run's `etcdVerifyEnv`, which `EtcdVerifyOff` says
is `etcdVerifyOffValue`) and
`strings.ToLower`'s (`strings.lowersTo`).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.IsVerificationEnabled
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

theorem verify.IsVerificationEnabled.wp_proof (hGetenv : os.Getenv.spec (GF := GF) (hG := hG))
    (hLower : strings.ToLower.spec (GF := GF) (hG := hG)) :
    verify.IsVerificationEnabled.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  wp_apply hGetenv as %v %Hoff
  wp_apply hLower as %lv %Hlv
  by_cases hall : lv = go!"all"
  · rw [decide_eq_true hall]
    wp_auto
    iapply HΦ
    ipureintro
    intro Hv
    obtain ⟨h1, -, -⟩ : etcdVerifyOffValue v := Hoff (by first | rfl | trivial) Hv
    have := (Hlv go!"all" (by decide)).1 hall
    simp [h1] at this
  · rw [decide_eq_false hall]
    wp_auto
    wp_apply hLower as %av %Hav
    iapply HΦ
    ipureintro
    intro Hv
    obtain ⟨-, h2, h3⟩ : etcdVerifyOffValue v := Hoff (by first | rfl | trivial) Hv
    intro ht
    simp only [decide_eq_false_iff_not]
    intro heq
    rcases ht with rfl | rfl
    · have hav : av = go!"assert" := (Hav go!"assert" (by decide)).2 (by decide)
      have := (Hlv go!"assert" (by decide)).1 (heq.trans hav)
      simp [h2] at this
    · have hav : av = go!"lock" := (Hav go!"lock" (by decide)).2 (by decide)
      have := (Hlv go!"lock" (by decide)).1 (heq.trans hav)
      simp [h3] at this

end proof

end EtcdGrove
end Perennial
