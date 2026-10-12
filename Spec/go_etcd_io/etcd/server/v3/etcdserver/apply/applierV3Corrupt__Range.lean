/-
`apply.applierV3Corrupt.Range` (corrupt.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`a.Range(r)`**: `ErrCorrupt`; nothing read. -/
abbrev apply.applierV3Corrupt.Range.spec : Prop :=
  ∀ (E : AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.corruptIs p inner ∗
      apply.rangePre E (.corrupt c) (interface.mkOk (go.GoType.PointerType applierV3Corrupt.ty) #p) r rq o log }}
    (App (Val (p @!! go.GoType.PointerType applierV3Corrupt.ty @!! go!"Range")) (Val #r))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      apply.rangePost E (.corrupt c) (interface.mkOk (go.GoType.PointerType applierV3Corrupt.ty) #p) rq o log resp err }}

end spec

end EtcdGrove
end Perennial
