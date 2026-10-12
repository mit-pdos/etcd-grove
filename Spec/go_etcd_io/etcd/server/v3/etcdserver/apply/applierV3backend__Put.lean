/-
`apply.applierV3backend.Put` (backend.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`a.Put(p)`**: `txn.Put(context.TODO(), lg, lessor, kv, p)` at the sole writer of `log`: the lease not found or the key missing (rejected by the backend), or the put committed as the client's put on `log`'s state (`backendStep`); the lease written known. -/
abbrev apply.applierV3backend.Put.spec : Prop :=
  ∀ (E : AEnv GF) (p r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log)
    (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.backendIs E p ∗
      apply.putPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) r rq o log Pre Q Post }}
    (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"Put")) (Val #r))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      apply.kvPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) rq log (apply.putAnswerIs log o resp err) Pre Post }}

end spec

end EtcdGrove
end Perennial
