/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.compareInt64

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.compareInt64.wp_proof : txn.compareInt64.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  wp_auto
  wp_if_destruct
  · have h : sint.Z a < sint.Z b := by simpa using Hif.symm
    have e : int64Cmp a b = -1 := by simp [int64Cmp, cmpSign, h]
    rw [e] at *
    iapply HΦ; itrivial
  · have h : ¬ sint.Z a < sint.Z b := by simpa using Hif
    wp_if_destruct
    · have h2 : sint.Z b < sint.Z a := by simpa using Hif.symm
      have hne : a ≠ b := by intro e; subst e; omega
      have e : int64Cmp a b = 1 := by simp [int64Cmp, cmpSign, h, hne]
      rw [e] at *
      iapply HΦ; itrivial
    · have h2 : ¬ sint.Z b < sint.Z a := by simpa using Hif
      have he : a = b := by
        apply BitVec.toInt_inj.1
        unfold sint.Z at h h2; omega
      subst he
      have e : int64Cmp a a = 0 := by simp [int64Cmp, cmpSign]
      rw [e] at *
      iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
