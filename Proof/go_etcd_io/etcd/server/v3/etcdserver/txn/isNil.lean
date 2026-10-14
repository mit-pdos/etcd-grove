/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart); unit P4 (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.isNil
public import Spec.reflect.ValueOf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.isNil.wp_proof (hVO : reflect.ValueOf.spec (GF := GF) (hG := hG)) :
    txn.isNil.spec (GF := GF) (hG := hG) := by
  intro T p
  wp_start
  wp_auto
  wp_apply hVO as %v #HIsNil
  wp_apply HIsNil
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
