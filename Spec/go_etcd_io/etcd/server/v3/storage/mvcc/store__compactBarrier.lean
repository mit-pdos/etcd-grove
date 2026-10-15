/-
`store.compactBarrier` (`kvstore.go`) (2026-10-13, unit 5a).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.compactBarrier(ctx, ch)` with the close right on `ch` (closed with `Q`, which holds): if
the context is cancelled, nothing when the store is stopped, else (under `s.mu`) another barrier
job scheduled with the right; if not, `ch` closed. -/
abbrev mvcc.store.compactBarrier.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (ch : GoChan) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeStop s ∗ mvcc.barrierCtx ctx cd ∗ mvcc.compactCloser ch Q ∗ □ Q }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compactBarrier"))
      (Val #(GoInterface.ok ctx))) (Val #ch))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
