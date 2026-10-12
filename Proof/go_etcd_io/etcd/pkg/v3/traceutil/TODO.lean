/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/TODO.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO

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

theorem traceutil.TODO.wp_proof : traceutil.TODO.spec (GF := GF) (hG := hG) := by
  wp_start as -
  (try wp_auto)
  wp_alloc t as Ht
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  (try wp_auto)
  iapply HΦ
  ipureintro
  exact Hnn

end proof

end EtcdGrove
end Perennial
