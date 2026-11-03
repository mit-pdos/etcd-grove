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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`a.newHeader()`**: a fresh `ResponseHeader` (the cluster's `ID`, the raft status's `MemberID`, `Term`, `Leader`, the KV's `Rev()`: `store.Rev` at the sole writer, whose reader slots and tokens it borrows). The post (the lease-grant stage, 2.11a, 2026-11-03): the
header's four id fields owned (`hdrFields`), its `Revision` the sole writer's log's last revision,
that log certified (`certOk`) and within the writer's bounds. -/
abbrev apply.applierV3backend.newHeader.spec : Prop :=
  ∀ (E : AEnv GF) (p : Loc) (log : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.backendIs E p ∗
      mvcc.storeReader E.s E.γ ∗ txn.kvWriter E.s E.γ log }}
    (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"newHeader")) (Val #()))
  {{ (h : Loc), RET #h; mvcc.storeReader E.s E.γ ∗ txn.kvWriter E.s E.γ log ∗ ⌜h ≠ null⌝ ∗
      apply.hdrFields h ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ W64 ((log.length : Int) - 1) ∗
      mvcc.certOk E.γ log ∗ ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63⌝ }}

end spec

end EtcdGrove
end Perennial
