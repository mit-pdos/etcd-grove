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

/-- `s.LinearizableReadNotify(ctx)`, a one-line delegation to the read loop's (`isRead`, met by
`read.NewRead`'s result, the request path's unit 4a): `nil` only once the applied index reached
the committed index `c` the caller knew of (`readIndexOk`), else an error the gRPC layer can take;
the caller's reader slot of the read loop's lock (`readReader`) is given back. -/
abbrev EtcdServer.LinearizableReadNotify.spec : Prop :=
  ∀ (s r : Loc) (γr : ReadNames) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (c : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvReadAddr s ↦□ r ∗ isRead r γr ∗ mvcc.txnCtx ctx cd ∗ committedAtLeast γr c ∗
      readReader r γr }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"LinearizableReadNotify"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; readReader r γr ∗ applyErrIs err ∗
      (⌜err = GoInterface.nil⌝ -∗ readIndexOk γr c) }}

end spec

end EtcdGrove
end Perennial
