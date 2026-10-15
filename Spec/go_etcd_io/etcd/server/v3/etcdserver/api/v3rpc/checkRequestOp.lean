/-
`v3rpc.checkRequestOp` (`key.go`). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`checkRequestOp(u, n)`**: `nil` iff the operation `u` passes at the budget `n`
(`opCheck`: a range, put, delete by its check, a nested transaction by `checkTxnRequest`, an
empty one never: `ErrGRPCKeyNotFound`), else the `rpctypes` error `opCheck` names. -/
abbrev v3rpc.checkRequestOp.spec : Prop :=
  ∀ (p : Loc) (u : v3rpc.ReqOp) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.reqOpIs p u }}
    (App (App (Val (@! v3rpc.checkRequestOp)) (Val #p)) (Val #n))
  {{ (err : GoInterface), RET #err; v3rpc.checkRes (v3rpc.opCheck (sint.Z n) u) err }}

end spec

end EtcdGrove
end Perennial
