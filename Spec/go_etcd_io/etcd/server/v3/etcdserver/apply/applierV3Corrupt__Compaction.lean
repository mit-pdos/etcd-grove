/-
`apply.applierV3Corrupt.Compaction` (corrupt.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`a.Compaction(r)`**: `ErrCorrupt`, no response, channel or trace; nothing compacted. -/
abbrev apply.applierV3Corrupt.Compaction.spec : Prop :=
  ∀ (p r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply }}
    (App (Val (p @!! go.GoType.PointerType applierV3Corrupt.ty @!! go!"Compaction")) (Val #r))
  {{ (resp : Loc) (ch : GoChan) (trace : Loc) (err : GoInterface),
      RET (PairV (PairV (PairV #resp #ch) #trace) #err);
      ⌜resp = null ∧ ch = chan.nil ∧ trace = null⌝ ∗
      txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCorrupt err }}

end spec

end EtcdGrove
end Perennial
