/-
`s.FirstCommitInTermNotify()` (`server.go`). Lean-first (no Rocq counterpart); the request path's unit 4b
(2026-10-13): a method of the read loop's `server` interface (`read/Inv.lean`, `isReadServer`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Spec.go_etcd_io.etcd.pkg.v3.notify.Notifier__Receive

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.FirstCommitInTermNotify()`: `s.firstCommitInTerm.Receive()`, with a reader slot of the
notifier. -/
abbrev EtcdServer.FirstCommitInTermNotify.spec : Prop :=
  ∀ (s n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvFirstCommitAddr s ↦□ n ∗ notifyReader n }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"FirstCommitInTermNotify"))
      (Val #()))
  {{ (ch : Loc), RET #ch; notifyReader n ∗ notifyChan ch }}

end spec

end EtcdGrove
end Perennial
