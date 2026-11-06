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

/-- **`a.newHeader()`**: a fresh `ResponseHeader` (the cluster's `ID`, the raft status's `MemberID`, `Term`, `Leader`, the KV's `Rev()`: `KV.Rev.contract` at the writer's read update, `envAus`; strict M1, 2026-11-05: the
thread's token and the writer's half in place of mvcc's reader slots). The post (the lease-grant stage, 2.11a, 2026-11-03): the
header's four id fields owned (`hdrFields`), its `Revision` the writer's log's last revision,
that log witnessed (`E.Nx`, the server's `kvNx`; the merge of `lean`, 2026-11-06: in place of mvcc's
`certOk`, from `envAus`'s writer facts) and within the writer's bounds. -/
abbrev apply.applierV3backend.newHeader.spec : Prop :=
  ∀ (E : AEnv GF) (p : Loc) (log : mvcc.Log) (c : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.backendIs E p ∗
      threadTok ∗ srvApi.wSt E.γs log c }}
    (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"newHeader")) (Val #()))
  {{ (h : Loc), RET #h; threadTok ∗ srvApi.wSt E.γs log c ∗ ⌜h ≠ null⌝ ∗
      apply.hdrFields h ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ W64 ((log.length : Int) - 1) ∗
      E.Nx log ∗ ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63⌝ }}

end spec

end EtcdGrove
end Perennial
