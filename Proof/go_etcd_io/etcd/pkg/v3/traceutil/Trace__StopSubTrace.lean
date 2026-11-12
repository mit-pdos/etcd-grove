/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__StopSubTrace.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__StopSubTrace

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

theorem traceutil.Trace.StopSubTrace.wp_proof :
    traceutil.Trace.StopSubTrace.spec (GF := GF) (hG := hG) := by
  intro t e fields
  wp_start as ⟨Ht, Hf⟩
  iunfold traceutil.ownTrace at Ht
  icases Ht with ⟨%v, %ss, Ht, Hfs, Hss, Hcap, Hsf, %He⟩
  wp_auto
  wp_apply wp_slice_literal (V := traceutil.step)
    [({ time' := zero_val _root_.Perennial.time.Time, msg' := zero_val GoString, fields' := fields, isSubTraceStart' := false, isSubTraceEnd' := true } : traceutil.step)]
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  (try wp_auto)
  wp_apply wp_slice_append (V := traceutil.step) _ _ _ _ _ $$ [$Hss $Hcap $Hsl2]
    as %sl3 ⟨Hss, Hcap, -⟩
  (try wp_auto)
  iapply HΦ
  iunfold traceutil.ownTrace
  iexists _, _
  (try simp only)
  iframe Ht Hfs Hss Hcap
  isplitl [Hsf Hf]
  · iapply BigSepL.bigSepL_snoc.2
    iframe
  ipureintro; exact He

end proof

end EtcdGrove
end Perennial
