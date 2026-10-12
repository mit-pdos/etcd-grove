/-
`s.LinearizableReadNotify(ctx)` (`interface.go`... `server.go`): `s.read.LinearizableReadNotify(ctx)`, over the read loop's contract (`isRead`).
Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.LinearizableReadNotify(ctx)`, a one-line delegation to the read loop's (`isRead`, the
contract until unit 4 proves `read/read.go`): `nil` only once the applied index reached the
committed index `c` the caller knew of (`readIndexOk`), else an error the gRPC layer can take. -/
abbrev EtcdServer.LinearizableReadNotify.spec : Prop :=
  ∀ (s r : Loc) (γr : ReadNames) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (c : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvReadAddr s ↦□ r ∗ isRead r γr ∗ mvcc.txnCtx ctx cd ∗ committedAtLeast γr c }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"LinearizableReadNotify"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; applyErrIs err ∗
      (⌜err = GoInterface.nil⌝ -∗ readIndexOk γr c) }}

end spec

end EtcdGrove
end Perennial
