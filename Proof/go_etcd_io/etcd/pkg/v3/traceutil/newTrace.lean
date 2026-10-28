/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/newTrace.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.newTrace

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

theorem traceutil.newTrace.wp_proof : traceutil.newTrace.spec (GF := GF) (hG := hG) := by
  intro op lg fields
  wp_start as Hf
  wp_auto
  wp_apply time.wp_Now as %now -
  (try wp_auto)
  irename «$r0» => Ht
  generalize «$r0_ptr» = t at *
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  (try wp_auto)
  iapply HΦ
  isplitr
  · ipureintro; exact Hnn
  iunfold traceutil.ownTrace
  iexists _, []
  iframe Ht Hf
  isplitl []
  · iapply ownSlice_nil
  isplitl []
  · iapply ownSliceCap_nil
  isplitl []
  · iapply BigSepL.bigSepL_nil.2
    iempintro
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
