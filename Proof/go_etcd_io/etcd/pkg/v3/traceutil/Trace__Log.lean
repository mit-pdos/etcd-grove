/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__Log.lean`. Lean-first (no Rocq counterpart);
etcd PR #22242 (2026-10-17).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Log
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__LogWithStepThreshold

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

theorem traceutil.Trace.Log.wp_proof
    (hLog : traceutil.Trace.LogWithStepThreshold.spec (GF := GF) (hG := hG)) :
    traceutil.Trace.Log.spec (GF := GF) (hG := hG) := by
  intro t e
  wp_start as Ht
  wp_auto
  wp_apply hLog t e _ $$ [Ht]
  · iframe #; iexact Ht
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
