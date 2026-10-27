/-
`v3rpc.kvServer.Compact` (`key.go`): the KV service's `Compact`, guarded by the admin guard
(`AuthAdmin.isPermitted`). Lean-first (no Rocq counterpart); the auth plan's A2 (2026-10-23),
vocabulary `v3rpc/InvAuthAdmin.lean` and `v3rpc/InvKV.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvAuthAdmin

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

/-- `s.Compact(ctx, r)`: `s.aa.isPermitted(ctx)` (the `*AuthAdmin` `aa` of the `*kvServer`:
`NewKVServer`'s `&AuthAdmin{s}`, a premise until `kvServerIs` records it), then the server's
`Compact` (the guarded contract `compactOk`: callable only with the token `adminRes` of the
request's auth info), whose header the handler fills; the outcome `compactOut`. -/
abbrev v3rpc.kvServer.Compact.spec : Prop :=
  ∀ (p s : Loc) (A : v3rpc.KVAns GF) (cid mid n : w64) (aa : Loc) (E : apply.AEnv GF)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (Pin : IProp GF)
    (Q : Loc → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.kvServerIs p s A cid mid n ∗
      structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer go!"aa" p ↦□ aa ∗
      v3rpc.authAdminIs aa s E ∗ srvAdminNilOk s E ∗ mvcc.txnCtx ctx cd ∗ E.RD ∗ Pin ∗
      v3rpc.compactOk s E A Pin (GoInterface.ok ctx) r Q }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.kvServer.ty @!! go!"Compact"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); E.RD ∗
      v3rpc.compactOut A cid mid Pin Q resp err }}

end spec

end EtcdGrove
end Perennial
