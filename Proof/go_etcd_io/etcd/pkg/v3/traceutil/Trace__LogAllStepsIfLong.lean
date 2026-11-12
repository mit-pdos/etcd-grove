/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__LogAllStepsIfLong.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__LogAllStepsIfLong
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__LogWithStepThreshold

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

theorem traceutil.Trace.LogAllStepsIfLong.wp_proof
    (hLog : traceutil.Trace.LogWithStepThreshold.spec (GF := GF) (hG := hG)) :
    traceutil.Trace.LogAllStepsIfLong.spec (GF := GF) (hG := hG) := by
  intro t e d
  wp_start as Ht
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  iunfold traceutil.ownTrace at Ht
  icases Ht with ⟨%v, %ss, Ht, Hfs, Hss, Hcap, Hsf, %He⟩
  wp_auto
  wp_apply _root_.Perennial.time.wp_Since as %el -
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    wp_apply hLog t e _ $$ [Ht Hfs Hss Hcap Hsf]
    · iframe #
      iunfold traceutil.ownTrace
      iexists _, _
      (try simp only)
      iframe
      ipureintro; exact He
    (try wp_auto)
    iapply HΦ
    itrivial
  · (try wp_auto)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
