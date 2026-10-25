/-
`v3rpc.requestLogFields` (`v3rpc/interceptor.go`, PR etcd#21401). Lean-first (no Rocq counterpart);
the vocabulary is `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvQuota.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvQuota

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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`requestLogFields(req)`** returns a slice of `zap.Field`s summarizing `req` when `req`
satisfies `learnerReqOk req` (reads the fields of `*RangeRequest`, `*PutRequest`,
`*DeleteRangeRequest`, or `*TxnRequest`, or returns an empty slice for any other request type). -/
abbrev v3rpc.requestLogFields.spec : Prop :=
  ∀ (req : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.learnerReqOk req }}
    (App (Val (@! v3rpc.requestLogFields)) (Val #req))
  {{ (sl : GoSlice), RET #sl; True }}

end spec

end EtcdGrove
end Perennial
