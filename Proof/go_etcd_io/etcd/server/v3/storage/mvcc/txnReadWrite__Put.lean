/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__Put


@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.txnReadWrite.Put.wp_proof : mvcc.txnReadWrite.Put.spec (GF := GF) (hG := hG) := by
  intro trw key value lease Φ
  iintro ⟨-, Hstuck⟩
  rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"Put")]
  wp_call
  (try wp_auto)
  wp_apply wp_panic
  iapply Hstuck

end proof

end EtcdGrove
end Perennial
