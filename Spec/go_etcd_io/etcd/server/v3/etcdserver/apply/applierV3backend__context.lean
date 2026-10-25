/-
`apply.applierV3backend.context` (backend.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`a.context()`**: constructs `txn.TxnContext` from `a.options` (`Logger`, `Lessor`, `KV`,
`TxnModeWriteWithSharedBuffer`), preserving the backend's invariants on the returned fields. -/
abbrev apply.applierV3backend.context.spec : Prop :=
  ∀ (E : AEnv GF) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.backendIs E p }}
    (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"context")) (Val #()))
  {{ (tc : go_etcd_io.etcd.server.v3.etcdserver.txn.TxnContext), RET #tc;
      ⌜tc.Logger' ≠ null⌝ ∗ txn.isKV tc.KV' E.s E.γ ∗ mvcc.hookOk E.γ E.P E.f ∗
      txn.isTxnLessor tc.Lessor' E.γ.leases }}

end spec

end EtcdGrove
end Perennial
