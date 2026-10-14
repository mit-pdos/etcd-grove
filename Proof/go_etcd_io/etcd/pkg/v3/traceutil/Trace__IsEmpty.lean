/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__IsEmpty.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__IsEmpty

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

theorem traceutil.Trace.IsEmpty.wp_proof :
    traceutil.Trace.IsEmpty.spec (GF := GF) (hG := hG) := by
  intro t e
  wp_start as Ht
  iunfold traceutil.ownTrace at Ht
  icases Ht with ⟨%v, %ss, Ht, Hfs, Hss, Hcap, Hsf, %He⟩
  wp_auto
  rw [He]
  iapply HΦ
  iunfold traceutil.ownTrace
  iexists _, _
  (try simp only)
  iframe
  ipureintro; exact He

end proof

end EtcdGrove
end Perennial
