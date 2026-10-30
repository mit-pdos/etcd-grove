/-
`v3rpc.watchServer.Watch` (`watch.go`): the watch slice's server hop. Lean-first (no Rocq counterpart); the
vocabulary is `v3rpc/InvWatchStream.lean` and `v3rpc/InvWatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`ws.Watch(stream)`**: a run on a fresh server end of a stream (`srvStreamIs` with both
tokens at the empty queues), whose content of the responses sent down is the watch server's
(`watchStreamSpec`: the handler's `Dn` is `watchDn`), the client's content of its requests
restricted with a watch token per create request (`upOk`), the stream's auxiliary name (set to
the run's ghost names, `auxOf`; the watch slice's unit W-C) and the run's resources
(`watchRunSlot`): it returns, with the stream specification. The specification is at the token of
the run's context `ci` (`auth.ctxTokenOf`; G2, 2026-10-30): each create's check passed for it
(`watchAuthed`). -/
abbrev v3rpc.watchServer.Watch.spec : Prop :=
  ∀ (p : Loc) (R : v3rpc.WSrv GF) (st : GoInterface) (γs : v3rpc.StreamNames)
    (Up : Nat → v3rpc.WatchReqM → IProp GF) (Dn : Nat → v3rpc.WatchRespM → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.isWatchServer p R ∗
      v3rpc.srvStreamIs st γs v3rpc.pbWatchRequest v3rpc.pbWatchResponse Up Dn ci cd ∗
      v3rpc.watchStreamSpec γs R.γ R.s (auth.ctxTokenOf (GoInterface.ok ci)) R.cid R.mid Dn ∗ v3rpc.upOk R.γ Up ∗
      v3rpc.srvRecvTok (Req := v3rpc.pbWatchRequest) γs [] ∗
      v3rpc.srvSendTok (Rep := v3rpc.pbWatchResponse) γs [] ∗ v3rpc.streamAuxTok γs ∗
      v3rpc.watchRunSlot R }}
    (App (Val (p @!! go.GoType.PointerType v3rpc.watchServer.ty @!! go!"Watch")) (Val #st))
  {{ (err : GoInterface), RET #err; v3rpc.watchStreamSpec γs R.γ R.s (auth.ctxTokenOf (GoInterface.ok ci)) R.cid R.mid Dn }}

end spec

end EtcdGrove
end Perennial
