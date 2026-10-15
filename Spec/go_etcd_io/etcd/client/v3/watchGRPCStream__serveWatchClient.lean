/-
`(*clientv3.watchGRPCStream).serveWatchClient(wc)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `w.serveWatchClient(wc)` on the client end of a gRPC watch stream with its receiver's token:
forwards every response it receives, in order, on `respc` (the producer's side: the `k`th
element is the stream's `k`th response, `respcElem`), until the receive fails (its error to
`errc`) or the stream is done (`donec`). -/
abbrev watchGRPCStream.serveWatchClient.spec : Prop :=
  ∀ (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) (wc : GoInterface) (γs : StreamNames)
    (Dn : Nat → v3rpc.WatchRespM → IProp GF) (cd' : context.ContextDesc (IProp GF))
    (γr : SpscNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isWGS V G callSl ∗
      v3rpc.cliWatchStreamIs wc γs (v3rpc.watchUp V.R.γ) Dn cd' ∗
      cliRecvTok (Rep := v3rpc.pbWatchResponse) γs [] ∗
      isSpsc γr G.respc (respcElem γs Dn) (fun _ => iprop(True)) ∗
      spscProducer γr ([] : List Loc) }}
    (App (Val (G.wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"serveWatchClient")) (Val #wc))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
