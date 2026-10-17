/-
`(*clientv3.watchGRPCStream).enqueueCreateReq(req)` (`client/v3/watch.go`, added by etcd-io/etcd#21065;
`notes/pr-verify/etcd-21065.md`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatchSend

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`w.enqueueCreateReq(req)`** by `run` (the create queue's producer, its channel open): puts
the request (with what the server asks of it, `sendElem`) on the create queue, waiting for room,
or gives up when the stream is done (`donec`, its context), the request then dropped. -/
abbrev watchGRPCStream.enqueueCreateReq.spec : Prop :=
  ∀ (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) (Q : SendQ) (sent : List Loc) (req : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isWGS V G callSl ∗
      sendQIs V G.wgs Q ∗ spscProducer Q.γc sent ∗ sendElem V 0 req }}
    (App (Val (G.wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"enqueueCreateReq")) (Val #req))
  {{ RET #(); ∃ sent' : List Loc, spscProducer Q.γc sent' ∗ ⌜sent' = sent ++ [req] ∨ sent' = sent⌝ }}

end spec

end EtcdGrove
end Perennial
