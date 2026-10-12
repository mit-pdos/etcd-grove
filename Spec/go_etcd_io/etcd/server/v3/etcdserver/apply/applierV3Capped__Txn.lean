/-
`apply.applierV3Capped.Txn` (capped.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`a.Txn(rt, skip)`**: `ErrNoSpace` if the request costs (`BackendQuota.Cost`), else the inner applier's `Txn`. -/
abbrev apply.applierV3Capped.Txn.spec : Prop :=
  ∀ (E : AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (skip : Bool) (rq : IRRModel) (t : TxnModel)
    (log : mvcc.Log) (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.cappedIs p inner ∗ apply.applierSpec E c inner ∗
      apply.txnPre E (.capped c) (interface.mkOk (go.GoType.PointerType applierV3Capped.ty) #p) r rq t log Pre Q Post }}
    (App (App (Val (p @!! go.GoType.PointerType applierV3Capped.ty @!! go!"Txn")) (Val #r)) (Val #skip))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      apply.kvPost E (.capped c) (interface.mkOk (go.GoType.PointerType applierV3Capped.ty) #p) rq log (apply.txnAnswerIs log t skip resp err) Pre Post }}

end spec

end EtcdGrove
end Perennial
