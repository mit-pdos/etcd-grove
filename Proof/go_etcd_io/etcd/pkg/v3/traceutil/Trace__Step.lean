/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__Step.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step

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

theorem traceutil.Trace.Step.wp_proof : traceutil.Trace.Step.spec (GF := GF) (hG := hG) := by
  intro t e msg fields
  wp_start as ⟨Ht, Hf⟩
  iunfold traceutil.ownTrace at Ht
  icases Ht with ⟨%v, %ss, Ht, Hfs, Hss, Hcap, Hsf, %He⟩
  wp_auto
  cases hd : v.stepDisabled'
  · wp_auto
    wp_apply time.wp_Now as %now -
    wp_apply wp_slice_literal (V := traceutil.step)
      [({ time' := now, msg' := msg, fields' := fields, isSubTraceStart' := false, isSubTraceEnd' := false } : traceutil.step)]
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
  · wp_auto
    iapply HΦ
    iunfold traceutil.ownTrace
    iexists _, _
    (try simp only)
    iframe
    ipureintro; exact He

end proof

end EtcdGrove
end Perennial
