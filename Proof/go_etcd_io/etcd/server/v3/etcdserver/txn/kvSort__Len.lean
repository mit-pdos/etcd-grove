/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.kvSort__Len

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.kvSort.Len.wp_proof : txn.kvSort.Len.spec (GF := GF) (hG := hG) := by
  intro ks sl ps dq
  wp_start as ⟨#Hf, Hs⟩
  wp_auto
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have : sl.len = W64 (ps.length : Int) := by rw [Hl.1, mvcc.W64_sint_nat _ Hl.2]
  rw [this]
  iapply HΦ
  iexact Hs

end proof

end EtcdGrove
end Perennial
