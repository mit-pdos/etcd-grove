/-
`apply.applierV3backend.newHeader` (backend.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Chain.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`a.newHeader()`**: a fresh `ResponseHeader` (the cluster's `ID`, the raft status's `MemberID`, `Term`, `Leader`, the KV's `Rev()`: `store.Rev` at the sole writer, whose reader slots and tokens it borrows). -/
abbrev apply.applierV3backend.newHeader.spec : Prop :=
  ∀ (E : AEnv GF) (p : Loc) (log : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.backendIs E p ∗
      mvcc.storeReader E.s E.γ ∗ txn.soleWriter E.γ log }}
    (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"newHeader")) (Val #()))
  {{ (h : Loc), RET #h; mvcc.storeReader E.s E.γ ∗ txn.soleWriter E.γ log ∗ ⌜h ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
