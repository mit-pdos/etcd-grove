/-
Proof of `Spec/github_com/prometheus/client_golang/prometheus/gauge__Set.lean`, over the real body
(prove-ps2-metrics, 2026-11-22).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.gauge__Set
public import Perennial.Proof.math.Link
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode prometheus.metric

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.prometheus.client_golang.prometheus.Assumptions]

theorem prometheus.gauge.Set.wp_proof : prometheus.gauge.Set.spec (GF := GF) (hG := hG) := by
  intro l x
  wp_start as #Hcell
  ihave #Hmath : isPkgInit (PROP := IProp GF) pkg_id.math $$ []
  · iPkgInit
  wp_auto
  wp_apply math.wp_Float64bits
  wp_apply_core sync.atomic.wp_StoreUint64 $$ [] [HΦ]
  · iPkgInit
  iunfold gaugeCell at Hcell
  iinv Hcell with >Hi Hclose
  icases Hi with ⟨%b, Hb⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists b
  iframe Hb
  iintro Hb
  imod Hmask with -
  imod Hclose $$ [Hb] with -
  · inext; iexists x; iframe Hb
  imodintro
  wp_auto
  iapply HΦ
  try itrivial

end proof

end EtcdGrove
end Perennial
