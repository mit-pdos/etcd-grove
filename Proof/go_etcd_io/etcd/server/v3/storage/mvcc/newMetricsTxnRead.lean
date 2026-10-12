/-
Proof of `Spec/.../mvcc/newMetricsTxnRead.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newMetricsTxnRead


@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.newMetricsTxnRead.wp_proof : mvcc.newMetricsTxnRead.spec (GF := GF) (hG := hG) := by
  intro v
  wp_start
  (try wp_auto)
  wp_alloc mw as Hmw
  (try wp_auto)
  iapply HΦ
  iexists «$v0_ptr»
  iframe Hmw «$v0»

end proof

end EtcdGrove
end Perennial
