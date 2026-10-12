/-
`v3rpc.checkTxnRequest` (`key.go`). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`checkTxnRequest(r, n)`**: `nil` iff the transaction passes at the budget `n`
(`txnCheck`: at most `n` comparisons and operations per branch, non-empty comparison keys,
`checkRequestOp` of every operation at `n` less that width), else the `rpctypes` error
`txnCheck` names. -/
abbrev v3rpc.checkTxnRequest.spec : Prop :=
  ∀ (r : Loc) (cs : List CmpModel) (ts es : List v3rpc.ReqOp) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.txnReqIs r cs ts es }}
    (App (App (Val (@! v3rpc.checkTxnRequest)) (Val #r)) (Val #n))
  {{ (err : GoInterface), RET #err; v3rpc.checkRes (v3rpc.txnCheck (sint.Z n) cs ts es) err }}

end spec

end EtcdGrove
end Perennial
