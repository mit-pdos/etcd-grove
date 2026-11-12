/-
`(*clientv3.watchGRPCStream).sendCloseSubstream(ws, resp)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `w.sendCloseSubstream(ws, resp)` (a goroutine of `closeSubstream`) with the producer's side of
the substream's `outc` and a canceled response with no events, a fresh zero header and a close
error grpc's `status` accepts: publishes it on `outc` (unless the watch's context is done or a
timeout passes first) and closes `outc`. -/
abbrev watchGRPCStream.sendCloseSubstream.spec : Prop :=
  ∀ (V : WEnv GF) (P : WsPrm GF) (wgs resp : Loc) (v : go_etcd_io.etcd.client.v3.WatchResponse),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wsIs V P ∗ outcProd P ∗
      wsF P.ws go!"outc" ↦ P.outc ∗
      resp ↦ v ∗ v.Header' ↦ (zero_val etcdserverpb.ResponseHeader) ∗
      ⌜v.Header' ≠ null ∧ v.Events' = slice.nil ∧ v.CompactRevision' = W64 0 ∧
        v.Canceled' = true ∧ v.Created' = false⌝ ∗ statusErrOk v.closeErr' }}
    (App (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"sendCloseSubstream")) (Val #P.ws)) (Val #resp))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
