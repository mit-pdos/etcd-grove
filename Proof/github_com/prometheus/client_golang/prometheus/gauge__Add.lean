/-
Proof of `Spec/github_com/prometheus/client_golang/prometheus/gauge__Add.lean`, over the real body
(prove-ps2-metrics, 2026-11-22).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.gauge__Add
public import Perennial.Proof.math.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Golang.Theory.Float

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

theorem prometheus.gauge.Add.wp_proof : prometheus.gauge.Add.spec (GF := GF) (hG := hG) := by
  intro l x
  wp_start as #Hcell
  ihave #Hmath : isPkgInit (PROP := IProp GF) pkg_id.math $$ []
  · iPkgInit
  iunfold gaugeCell at Hcell
  try wp_auto
  wp_for
  wp_apply_core sync.atomic.wp_LoadUint64 $$ [] [-]
  · iPkgInit
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
  · inext; iexists b; iframe Hb
  imodintro
  try wp_auto
  wp_apply math.wp_Float64frombits
  wp_apply wp_float64_add as %f -
  wp_apply math.wp_Float64bits
  wp_apply_core sync.atomic.wp_CompareAndSwapUint64 $$ [] [-]
  · iPkgInit
  iinv Hcell with >Hi Hclose
  icases Hi with ⟨%b', Hb⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists b', (DFrac.own 1)
  iframe Hb
  isplitr
  · ipureintro; split <;> rfl
  iintro Hb
  imod Hmask with -
  imod Hclose $$ [Hb] with -
  · inext; iexists _; iframe Hb
  imodintro
  try wp_auto
  wp_if_destruct
  · wp_for_post
    iapply HΦ
    try itrivial
  · wp_for_post
    iframe

end proof

end EtcdGrove
end Perennial
