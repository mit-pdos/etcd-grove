/-
`v3rpc.checkRangeStreamRequest` (`key.go`). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvKV.lean` and `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`checkRangeStreamRequest(r)`**: `checkRangeRequest`'s error, or, past it, a non-nil
`status` error (`Unimplemented`) for a sort other than the default or a revision filter
(`streamOk`), else `nil`. -/
abbrev v3rpc.checkRangeStreamRequest.spec : Prop :=
  ∀ (r : Loc) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ txn.rangeRequestIs r o }}
    (App (Val (@! v3rpc.checkRangeStreamRequest)) (Val #r))
  {{ (err : GoInterface), RET #err;
      match v3rpc.rangeCheck o with
      | some e => txn.errVarIs e.var err
      | none => ⌜err = GoInterface.nil ↔ v3rpc.streamOk o⌝ }}

end spec

end EtcdGrove
end Perennial
