/-
`clock.RealClock.After`, verified: k8s.io/utils/clock's code as released (`time.After(d)`, translated
with its body, `Code/k8s_io/utils/clock.toml`) over Perennial's verified `time` (`time.wp_After`).
Until 2026-11-28 a named hypothesis of the k8s results.
-/
module

public import Spec.k8s_io.utils.clock.RealClock__After
public import Perennial.Proof.time

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
variable [package_sem : k8s_io.utils.clock.Assumptions]

theorem clock.RealClock.After.wp_proof : clock.RealClock.After.spec (GF := GF) (hG := hG) := by
  intro c d
  wp_start
  ihave #Hti : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_alloc res as Hres
  wp_auto
  wp_apply time.After.spec_pkgInit time.wp_After d $$ [Hti] as %ch %γ #Hch
  iapply HΦ
  iexact Hch

end proof

end EtcdGrove
end Perennial
