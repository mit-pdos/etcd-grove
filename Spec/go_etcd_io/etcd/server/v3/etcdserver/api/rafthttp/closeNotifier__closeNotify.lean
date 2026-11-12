/-
`closeNotifier.closeNotify` (`http.go`; rafthttp stage 5e-2). Lean-first; the notifier: `rafthttp/CloseNotifier.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.CloseNotifier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`n.closeNotify()`**: its `done` channel, closed once `P` is handed over. -/
abbrev rafthttp.closeNotifier.closeNotify.spec : Prop :=
  ∀ (n : Loc) (γ : GName) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      cnRecv n γ P }}
    (App (Val (n @!! go.GoType.PointerType rafthttp.closeNotifier.ty @!! go!"closeNotify"))
      (Val #()))
  {{ (dc : GoChan), RET #dc; ∃ γc, ownBroadcastChan dc γc (cnQ γ P) .Unknown }}

end spec

end EtcdGrove
end Perennial
